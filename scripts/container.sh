cas_feedback_image_refresh=0
if [[ "$PWD" == /repos/* ]]; then
  root=$PWD
  incontainer() { "$@"; }
elif [[ "$PWD" == */sage-repos/_data/* ]]; then
  root=/repos/${PWD#*/sage-repos/_data/}
  export DOCKER_HOST="unix:///run/user/$(id -u)/docker.sock"
  CAS_FEEDBACK_IMAGE_DIGEST=$("$HOME/bin/docker" inspect --format '{{.Image}}' sage-research)
  export CAS_FEEDBACK_IMAGE_DIGEST
  cas_feedback_image_refresh=1
  incontainer() (
    cas_native_token=$(cat /proc/sys/kernel/random/uuid)
    cas_native_marker=/tmp/lean-cas-dsl-native-$cas_native_token
    cas_native_client=
    cas_native_interrupted=0
    cas_native_cleanup() {
      [[ "$cas_native_interrupted" == 0 ]] || return 0
      "$HOME/bin/docker" exec sage-research rm -f -- \
        "$cas_native_marker.pid" "$cas_native_marker.cancel" "$cas_native_marker.done" \
        >/dev/null 2>&1 || true
    }
    cas_native_interrupt() {
      local cas_native_signal=$1 cas_native_status=$2
      cas_native_interrupted=1
      trap '' INT TERM
      "$HOME/bin/docker" exec sage-research bash -c '
        printf "%s\n" "$2" > "$1.cancel"
        sent=0
        for attempt in {1..100}; do
          [[ ! -e "$1.done" ]] || break
          if [[ "$sent" == 0 && -r "$1.pid" ]]; then
            read -r group < "$1.pid"
            if grep -Fq -- "$1" "/proc/$group/cmdline" 2>/dev/null; then
              kill -s "$2" -- "-$group" 2>/dev/null || true
            fi
            sent=1
          fi
          sleep 0.05
        done
        if [[ -e "$1.done" ]]; then rm -f -- "$1.pid" "$1.cancel" "$1.done"; fi' \
        bash "$cas_native_marker" "$cas_native_signal" >/dev/null 2>&1 || true
      if [[ -n "$cas_native_client" ]]; then wait "$cas_native_client" || true; fi
      exit "$cas_native_status"
    }
    trap cas_native_cleanup EXIT
    trap 'cas_native_interrupt INT 130' INT
    trap 'cas_native_interrupt TERM 143' TERM
    "$HOME/bin/docker" exec -i -w "$root" \
      -e CAS_FEEDBACK_IMAGE_DIGEST="$CAS_FEEDBACK_IMAGE_DIGEST" sage-research \
      setsid --wait env --default-signal=INT,TERM bash -c '
        marker=$1
        shift
        trap '\''status=$?; printf "%s\n" "$status" > "$marker.done"'\'' EXIT
        trap '\''exit 130'\'' INT
        trap '\''exit 143'\'' TERM
        printf "%s\n" "$$" > "$marker.pid"
        if [[ -e "$marker.cancel" ]]; then
          read -r interrupted < "$marker.cancel"
          [[ "$interrupted" != INT ]] || exit 130
          exit 143
        fi
        "$@"
        exit "$?"' bash "$cas_native_marker" "$@" <&0 &
    cas_native_client=$!
    cas_native_status=0
    wait "$cas_native_client" || cas_native_status=$?
    exit "$cas_native_status"
  )
else
  echo "this checkout is not under /repos or the sage-repos volume: $PWD" >&2
  exit 2
fi

CAS_FEEDBACK_IMAGE_DIGEST=$(incontainer python3 - "$cas_feedback_image_refresh" <<'PY'
import json
import os
import re
import sys
import tempfile
from pathlib import Path

path = Path('/run/lean-cas-dsl/image.json')
instance = {
    'boot': Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
    'pid_namespace': os.readlink('/proc/1/ns/pid'),
    'init_started': Path('/proc/1/stat').read_text().rsplit(')', 1)[1].split()[19],
}
if sys.argv[1] == '1':
    image = os.environ.get('CAS_FEEDBACK_IMAGE_DIGEST', '')
    if re.fullmatch(r'sha256:[0-9a-f]{64}', image) is None:
        raise SystemExit('the running research container has no exact image digest')
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as output:
        temporary = Path(output.name)
        json.dump({'instance': instance, 'image_digest': image}, output)
        output.write('\n')
        output.flush()
        os.fsync(output.fileno())
    temporary.chmod(0o644)
    os.replace(temporary, path)
else:
    try:
        record = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        raise SystemExit('the research image must first be identified by the host launcher') from error
    if record.get('instance') != instance:
        raise SystemExit('the recorded image belongs to a different container instance')
    image = record.get('image_digest', '')
    if re.fullmatch(r'sha256:[0-9a-f]{64}', image) is None:
        raise SystemExit('the recorded research image digest is invalid')
    supplied = os.environ.get('CAS_FEEDBACK_IMAGE_DIGEST')
    if supplied is not None and supplied != image:
        raise SystemExit('the supplied image digest differs from the actual container image')
print(image)
PY
)
export CAS_FEEDBACK_IMAGE_DIGEST
