#!/bin/sh

REPO_URL="https://github.com/rocq-prover/rocq"

usage() {
  cat <<'EOF'
Usage: make-changelog.sh [options]

Without options, runs interactively (original behavior).

Options:
  -p, --pr NUM            PR number
  -c, --category CAT      Category prefix (e.g. "03" or "notations")
  -t, --type TYPE         Change type: Added/Changed/Deprecated/Fixed/Removed
                          (or just the first letter)
  -f, --fixes NUMS        Space-separated list of fixed issue numbers
  -d, --description TEXT  Description text (default: placeholder)
  -a, --author NAME       Author name (default: git config user.name)
      --auto              Guess --pr and --fixes from the current branch
  -h, --help              Show this help

In --auto mode, --category and --type are still required.
EOF
}

PR=""
category=""
type_input=""
fixes_list=""
description=""
author=""
auto=0
cli=0

while [ $# -gt 0 ]; do
  cli=1
  case "$1" in
    -p|--pr)          PR="$2"; shift 2;;
    -c|--category)    category="$2"; shift 2;;
    -t|--type)        type_input="$2"; shift 2;;
    -f|--fixes)       fixes_list="$2"; shift 2;;
    -d|--description) description="$2"; shift 2;;
    -a|--author)      author="$2"; shift 2;;
    --auto)           auto=1; shift;;
    -h|--help)        usage; exit 0;;
    *) printf 'Unknown option: %s\n\n' "$1" >&2; usage >&2; exit 1;;
  esac
done

branch=$(git rev-parse --abbrev-ref HEAD)

# Find the remote that points at the upstream rocq-prover/rocq repository.
# Falls back to "upstream", then "origin".
upstream_remote=$(git remote -v | awk '/rocq-prover\/rocq(\.git)?[[:space:]]/ {print $1; exit}')
if [ -z "$upstream_remote" ]; then
  if git remote | grep -qx upstream; then
    upstream_remote="upstream"
  else
    upstream_remote="origin"
  fi
fi

if [ "$auto" -eq 1 ]; then
  # Guess the PR number.
  if [ -z "$PR" ]; then
    PR=$(gh pr list --head "$branch" --json number --jq '.[0].number' 2>/dev/null || true)
    if [ -z "$PR" ] || [ "$PR" = "null" ]; then
      # No open PR: take the most recent issue/PR number and add 1.
      latest=$(gh api 'repos/rocq-prover/rocq/issues?state=all&per_page=1' \
                 --jq '.[0].number' 2>/dev/null || true)
      if [ -n "$latest" ] && [ "$latest" != "null" ]; then
        PR=$((latest + 1))
      fi
    fi
  fi

  # Guess fixed issues from commit messages since the merge-base with upstream master.
  if [ -z "$fixes_list" ]; then
    base=$(git merge-base "$upstream_remote/master" HEAD 2>/dev/null || true)
    if [ -n "$base" ]; then
      fixes_list=$(git log "$base"..HEAD --format='%B' \
        | grep -oiE '(fixes|closes):?[[:space:]]+#[0-9]+' \
        | grep -oE '[0-9]+' \
        | sort -un \
        | tr '\n' ' ')
    fi
  fi
fi

if [ "$cli" -eq 0 ]; then
  # Interactive mode (original behavior).
  printf "PR number? "
  read -r PR

  printf "Category? (type a prefix)\n"
  (cd doc/changelog && ls -d */)
  read -r category

  printf "Type? (type first letter)\n"
  printf "[A]dded \t[C]hanged \t[D]eprecated \t[F]ixed \t[R]emoved\n"
  read -r type_input

  printf "Fixes? (space separated list of bug numbers)\n"
  read -r fixes_list
fi

if [ -z "$PR" ]; then
  printf 'Error: PR number is required (use --pr or --auto).\n' >&2
  exit 1
fi

case "$type_input" in
  [Aa]|[Aa]dded)      type_full="Added";;
  [Cc]|[Cc]hanged)    type_full="Changed";;
  [Dd]|[Dd]eprecated) type_full="Deprecated";;
  [Ff]|[Ff]ixed)      type_full="Fixed";;
  [Rr]|[Rr]emoved)    type_full="Removed";;
  "") printf 'Error: type is required (use --type).\n' >&2; exit 1;;
  *) printf "Invalid input!\n" >&2; exit 1;;
esac

# Resolve the category directory. Accept an exact name, a leading prefix
# (e.g. "03"), or a substring of the descriptive part (e.g. "notations").
list_dirs() {
  for d in "$@"; do
    if [ -d "$d" ]; then printf '%s\n' "$d"; fi
  done
  return 0
}
candidates=$(list_dirs "doc/changelog/$category")
[ -z "$candidates" ] && candidates=$(list_dirs "doc/changelog/$category"*)
[ -z "$candidates" ] && candidates=$(list_dirs "doc/changelog/"*"$category"*)

if [ -n "$candidates" ]; then
  n=$(printf '%s\n' "$candidates" | grep -c .)
else
  n=0
fi
if [ "$n" -eq 0 ]; then
  printf 'Error: no category matching "%s" under doc/changelog/.\n' "$category" >&2
  printf 'Available categories:\n' >&2
  (cd doc/changelog && ls -d */) >&2
  exit 1
elif [ "$n" -gt 1 ]; then
  printf 'Error: category "%s" is ambiguous, matches:\n%s\n' "$category" "$candidates" >&2
  exit 1
fi
where=$candidates
where="${where}/${PR}-$(echo "$branch" | tr / -)-${type_full}.rst"

# shellcheck disable=SC2016
# the ` are regular strings, this is intended
fixes_string="$(echo $fixes_list | sed "s/ /~  and /g; s,\([0-9][0-9]*\),\`#\1 <$REPO_URL/issues/\1>\`_,g" | tr '~' '\n')"
if [ -n "$fixes_string" ]; then fixes_string="$(printf '\n  fixes %s,' "$fixes_string")"; fi

if [ -z "$author" ]; then author="$(git config user.name)"; fi

if [ -z "$description" ]; then
  description="Describe your change here but do not end with a period"
fi

# shellcheck disable=SC2016
# the ` are regular strings, this is intended
# use %s for the leading - to avoid looking like an option
printf '%s **%s:**\n  %s\n  (`#%s <%s/pull/%s>`_,%s\n  by %s).\n' \
  - "$type_full" "$description" "$PR" "$REPO_URL" "$PR" "$fixes_string" "$author" > "$where"

printf 'Name of created changelog file:\n'
printf '%s\n' "$where"

if [ "$cli" -eq 0 ]; then
  giteditor=$(git config core.editor)
  if [ "$giteditor" ]; then
      $giteditor "$where"
  elif [ "$EDITOR" ]; then
      $EDITOR "$where"
  else
      printf "Describe the changes in the above file\n"
  fi
fi
