# Sourced by the feedback scripts. Defines how a command reaches the Lean toolchain.
#
# The toolchain is in the research container `sage-research`. A checkout under the host volume
# `…/sage-repos/_data/<path>` is `/repos/<path>` there. Inside the container a command runs as it
# is; on the host it runs through `docker exec` at the same checkout.
#
# Sets `root` (the checkout's path in the container) and the function `incontainer`.

if [[ "$PWD" == /repos/* ]]; then
  root=$PWD
  incontainer() { "$@"; }
elif [[ "$PWD" == */sage-repos/_data/* ]]; then
  root=/repos/${PWD#*/sage-repos/_data/}
  export DOCKER_HOST="unix:///run/user/$(id -u)/docker.sock"
  incontainer() { "$HOME/bin/docker" exec -i -w "$root" sage-research "$@"; }
else
  echo "this checkout is not under /repos or the sage-repos volume: $PWD" >&2
  exit 2
fi
