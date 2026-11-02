"""Resolve repository pointers to the actual GitHub issue discussion.

Repository prose selects sources; it is never substituted for their contents.
Callers retain the returned documents in their existing review/assignment snapshot.
"""
import json
import os
import re
import urllib.request


REPOSITORY = 'dzackgarza/lean-cas-dsl'
WEB = 'https://github.com/' + REPOSITORY + '/issues/'
API = 'https://api.github.com/repos/' + REPOSITORY + '/issues/'
ISSUE_LINK = re.compile(re.escape(WEB) + r'([1-9][0-9]*)(?:#[-a-zA-Z0-9_]+)?(?=$|[\s)<>"\x27])')
POINTER_PATHS = ('AGENTS.md', 'CONTRIBUTING.md', 'INTENT.md', 'SPEC.md',
                 'specs/architecture.md', 'specs/computational-core-plan.md',
                 'custodian/review/prompt.md')


def issue_numbers(text):
    return sorted({int(match.group(1)) for match in ISSUE_LINK.finditer(text)})


def fetch_json(url):
    headers = {'Accept': 'application/vnd.github+json',
               'X-GitHub-Api-Version': '2022-11-28',
               'User-Agent': 'lean-cas-dsl-issue-context'}
    token = os.environ.get('GH_TOKEN') or os.environ.get('GITHUB_TOKEN')
    if token:
        headers['Authorization'] = 'Bearer ' + token
    request = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)


SOURCE_LINK = re.compile(r'https://github\.com/([A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9][A-Za-z0-9_.-]*)/issues/([1-9][0-9]*)(?:#issuecomment-([1-9][0-9]*))?\Z')


def source_reference(url):
    match = SOURCE_LINK.fullmatch(url)
    if not match:
        raise ValueError('assignment requires an exact GitHub issue or issue-comment URL: ' + url)
    return match.group(1), int(match.group(2)), int(match.group(3)) if match.group(3) else None


def source_record(item, url):
    try:
        return {key: item[key] for key in ('id', 'html_url', 'user', 'created_at', 'updated_at', 'body')}
    except KeyError as error:
        raise ValueError('issue source metadata is incomplete: ' + url) from error


def load_sources(sources):
    """Capture only the sources explicitly supplied for this operation.

    An exact comment reference fetches that comment alone. It never expands to
    the parent issue or its other discussions, which may belong to another role.
    """
    if not sources:
        raise ValueError('missing independently supplied issue/comment requirement sources')
    documents = {}
    for url in dict.fromkeys(sources):
        repository, number, comment_id = source_reference(url)
        api = 'https://api.github.com/repos/' + repository + '/issues/'
        issue_url = 'https://github.com/' + repository + '/issues/' + str(number)
        if comment_id is not None:
            item = fetch_json(api + 'comments/' + str(comment_id))
            if not isinstance(item, dict) or item.get('html_url') != url or item.get('issue_url') != api + str(number):
                raise ValueError('assignment comment is not the linked source: ' + url)
            if not isinstance(item.get('body'), str) or not item['body'].strip():
                raise ValueError('assignment comment body is unavailable: ' + url)
            snapshot = source_record(item, url)
        else:
            issue = fetch_json(api + str(number))
            if not isinstance(issue, dict) or issue.get('number') != number or issue.get('html_url') != issue_url or 'pull_request' in issue:
                raise ValueError('requirement source is not the linked issue: ' + url)
            if not isinstance(issue.get('body'), str) or not issue['body'].strip():
                raise ValueError('requirement issue body is unavailable: ' + url)
            comments = []
            page = 1
            while True:
                batch = fetch_json(api + str(number) + '/comments?per_page=100&page=' + str(page))
                if not isinstance(batch, list):
                    raise ValueError('requirement comments are unavailable: ' + url)
                comments.extend(batch)
                if len(batch) < 100:
                    break
                page += 1
            for item in comments:
                if not isinstance(item, dict) or item.get('issue_url') != api + str(number) or not isinstance(item.get('body'), str):
                    raise ValueError('comment does not belong to the linked issue: ' + url)
            ids = [item.get('id') for item in comments]
            if None in ids or len(ids) != len(set(ids)) or len(comments) != issue.get('comments'):
                raise ValueError('issue discussion changed or was incomplete during retrieval: ' + url)
            snapshot = dict(source_record(issue, url), number=number, title=issue['title'],
                            comments=[source_record(item, url) for item in comments])
        # Keep exact bodies and attribution. A fetched comment is not, merely by
        # being fetched, an owner ruling or permission for a different role.
        documents[url] = json.dumps(snapshot, ensure_ascii=False, sort_keys=True, indent=2)
    return documents


def load_documents(pointers):
    """Resolve trusted review pointers, not worker assignments or local prose."""
    numbers = sorted({number for text in pointers.values() for number in issue_numbers(text)})
    if not numbers:
        raise ValueError('requirement pointers contain no lean-cas-dsl issue links')
    return load_sources([WEB + str(number) for number in numbers])


def revision_pointers(revision):
    return {path: revision.read(path).decode() for path in revision.files()
            if path in POINTER_PATHS or path.startswith('specs/owner/')}


def directory_pointers(base):
    files = [base / path for path in POINTER_PATHS]
    files += sorted((base / 'specs' / 'owner').glob('*.md'))
    return {path.relative_to(base).as_posix(): path.read_text() for path in files if path.is_file()}


def render_documents(documents):
    return '\n\n'.join('<issue source=' + json.dumps(url) + '>\n' + body + '\n</issue>'
                       for url, body in documents.items())


def materialize_prompt(pointer, documents, out):
    """Use the exact linked comment from the already captured issue snapshot."""
    references = list(ISSUE_LINK.finditer(pointer.read_text()))
    if len(references) != 1:
        raise ValueError('review prompt must point to one issue comment')
    reference = references[0]
    url = reference.group(0)
    fragment = url.partition('#issuecomment-')[2]
    if not fragment.isdigit():
        raise ValueError('review prompt requires an exact issue-comment pointer')
    discussion = json.loads(documents[WEB + reference.group(1)])
    comments = [comment for comment in discussion['comments'] if comment['id'] == int(fragment)]
    if len(comments) != 1 or comments[0]['html_url'] != url or not comments[0]['body'].strip():
        raise ValueError('review prompt comment is unavailable in the captured discussion')
    out.mkdir(parents=True, exist_ok=True)
    prompt = out / 'review-prompt.txt'
    prompt.write_text(comments[0]['body'])
    (out / 'review-prompt-source.json').write_text(json.dumps(comments[0], ensure_ascii=False, sort_keys=True))
    return prompt
