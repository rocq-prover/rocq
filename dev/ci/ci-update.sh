#!/usr/bin/env bash

CI_QUIET=1

set +x

ci_dir="$(dirname "$0")"
. "${ci_dir}/scripts/ci-common.sh"

# [git_update <project>] will update the git repository associated to <project>
git_update()
{
  local project=$1
  local dest="${CI_BUILD_DIR}/$project"

  echo "Updating $project..."

  if [ ! -d "$dest" ]; then
    echo "Warning: update of $project skipped because $dest does not exist."
  else
    pushd "$dest" > /dev/null
    git remote update > /dev/null
    popd > /dev/null
  fi
}

git_update_all() {
  for project in "${projects[@]}"; do
    if [ -d "${CI_BUILD_DIR}/$project" ]; then
      git_update $project
    fi
  done
}

if [ -n "$1" ]; then
  git_update "$1"
else
  git_update_all
fi
