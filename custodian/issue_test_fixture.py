"""Mock public issue transport in source fixtures, including their child processes."""
import atexit
import io
import json
import os
from pathlib import Path
import re
import tempfile
import urllib.request


POINTER = ('[Assigned issue](https://github.com/dzackgarza/lean-cas-dsl/issues/24)\n'
           '[Review](https://github.com/dzackgarza/lean-cas-dsl/issues/10)\n')


def assignment(role):
    return {'role': role, 'sources': ['https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-100']}


def issue_response(request, **kwargs):
    url = request.full_url
    if url == 'https://api.github.com/repos/dzackgarza/lean-cas-dsl/issues/comments/100':
        value = {'id': 100, 'html_url': 'https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-100',
                 'issue_url': 'https://api.github.com/repos/dzackgarza/lean-cas-dsl/issues/24',
                 'body': 'fixture independently supplied requirement', 'user': {'login': 'independent-fixture'},
                 'created_at': '2026-01-01T00:00:00Z', 'updated_at': '2026-01-01T00:00:00Z'}
        return io.BytesIO(json.dumps(value).encode())
    match = re.fullmatch(r'https://api.github.com/repos/dzackgarza/lean-cas-dsl/issues/([1-9][0-9]*)(/comments\?per_page=100&page=([1-9][0-9]*))?', url)
    if not match:
        raise AssertionError('unexpected network request in issue fixture: ' + url)
    number = int(match.group(1))
    web = 'https://github.com/dzackgarza/lean-cas-dsl/issues/' + str(number)
    common = {'user': {'login': 'independent-fixture'}, 'created_at': '2026-01-01T00:00:00Z',
              'updated_at': '2026-01-01T00:00:00Z'}
    if match.group(2):
        # Supply the exact prompt-comment ids in the fixture pointer sources,
        # without contacting GitHub or changing production source selection.
        ids = set()
        root = Path(__file__).parent
        paths = [root / 'review/prompt.md', root.parent / 'AGENTS.md']
        for path in paths:
            if path.is_file():
                ids.update(int(value) for value in re.findall(r'issues/' + str(number) + r'#issuecomment-([0-9]+)', path.read_text()))
        value = [dict(common, id=identifier, html_url=web + '#issuecomment-' + str(identifier),
                      issue_url=url.partition('/comments')[0], body='Independent engineering review fixture; report the supplied outcome schema.')
                 for identifier in sorted(ids)] if match.group(3) == '1' else []
    else:
        comments = json.load(issue_response(urllib.request.Request(url + '/comments?per_page=100&page=1')))
        value = dict(common, id=number, number=number, html_url=web, title='Assigned fixture obligation',
                     body='Independently supplied fixed issue requirement.', comments=len(comments))
    return io.BytesIO(json.dumps(value).encode())


def install_fetcher():
    urllib.request.urlopen = issue_response


def install():
    install_fetcher()
    directory = tempfile.TemporaryDirectory(prefix='custodian-issue-fixture-')
    atexit.register(directory.cleanup)
    Path(directory.name, 'sitecustomize.py').write_text('from issue_test_fixture import install_fetcher\ninstall_fetcher()\n')
    paths = [directory.name, str(Path(__file__).resolve().parent)]
    if os.environ.get('PYTHONPATH'):
        paths.append(os.environ['PYTHONPATH'])
    os.environ['PYTHONPATH'] = os.pathsep.join(paths)
