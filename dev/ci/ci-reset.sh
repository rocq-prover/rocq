#!/usr/bin/env bash

CI_QUIET=1

set +x

ci_dir="$(dirname "$0")"
. "${ci_dir}/scripts/ci-common.sh"

# [git_reset <project>] will reset the repository for <project> to the upstream branch
git_reset()
{
  local project=$1

  # Special handling of iris reverse deps, see ci-iris.sh
  if [ "$project" = "iris" ]; then
    iris_CI_REF=$(grep -F '"rocq-iris-heap-lang"' < "${CI_BUILD_DIR}"/iris_examples/*-iris-examples.opam | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')
  [ -n "$iris_CI_REF" ] || { echo "Could not find Iris dependency version" && exit 1; }
  elif [ "$project" = "stdpp" ]; then
    stdpp_CI_REF=$(grep -F '"rocq-stdpp"' < "${CI_BUILD_DIR}/iris/rocq-iris.opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')
    [ -n "$stdpp_CI_REF" ] || { echo "Could not find stdpp dependency version" && exit 1; }
  fi

  local dest="${CI_BUILD_DIR}/$project"
  local ref_var="${project}_CI_REF"
  local ref="${!ref_var}"

  # Check whether it may be a submodule
  if [ -z "$ref" ]; then
    ref_var="${project}_CI_SUBMODULE_BRANCH"
    ref="${!ref_var}"
  fi

  echo "Resetting $project..."

  if [ ! -d "$dest" ]; then
    echo "Warning: reset of $project skipped because $dest does not exist."
  else if [ -z "$ref" ]; then
    echo "Warning: reset of $project skipped as no branch could be found."
  else
    # TODO: properly handle submodules
    pushd "$dest" > /dev/null
    # check that the reference is an actual branch
    local ref_hash=$(git rev-parse --verify --quiet "refs/heads/$ref")
    if [ -n "$ref_hash" ]; then
      git reset --hard --quiet
      git checkout $ref --quiet
      git reset --hard "origin/$ref" --quiet
      echo "$project reset to $ref ($ref_hash)"
    else if [ $(git rev-parse --verify --quiet "$ref") ]; then
    # if the reference is a hash just check it out
      git reset --hard --quiet
      git checkout $ref --quiet
      echo "$project reset to $ref"
    else
      echo "Warning: reset of $project skipped as $ref is not valid reference."
    fi
    fi
    popd > /dev/null
  fi
  fi
}

git_reset_all() {
  for project in "${projects[@]}"; do
    if [ -d "${CI_BUILD_DIR}/$project" ]; then
      git_reset $project
    fi
  done
}

if [ -n "$1" ]; then
  git_reset "$1"
else
  git_reset_all
fi
