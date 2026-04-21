#!/usr/bin/env bash

# integrate with make jobserver:
# if MAKEFLAGS contains -j and jobserver info,
# we consume the -j jobs (blocking until they're all available)
# and pass the -j $jobs on to our subcommand "$@"
# if there's no jobserver info we just run the subcommand "$@"

# DO NOT LET MAKE RUN THIS IN PARALLEL IT WILL DEADLOCK
# (ie use .NOTPARALLEL, a .NOTPARALLEL makefile recursively calling make
# (or any jobserver aware tool) does not block parallelism)

jobs=
server_in=
server_out=
mode=

for o in $MAKEFLAGS; do
  case "$o" in
    "n")
      echo "Skipping $* (make -n)"
      exit 0;;
    "-j"*)
      jobs=${o#-j}
      if [ "$jobs" = "" ]; then jobs=infinite; fi;;
    "--jobserver-auth=fifo:"*)
      server=${o#--jobserver-auth=fifo:}
      server_in=$server
      server_out=$server
      mode=fifo
      ;;
    "--jobserver-auth="*","*)
      server=${o#--jobserver-auth=}
      server_in=${server%,*}
      server_out=${server#*,}
      mode=pipes
      ;;
    "--jobserver-auth="*)
      >&2 echo "Unsupported jobserver mode ($o)"
      exit 1;;
  esac
done
export -n MAKEFLAGS

if ! [ "$mode" ]; then
  if [ "$jobs" = "" ]; then
    exec "$@"
  elif [ "$jobs" = 1 ]; then
    exec "$@" -j 1
  elif [ "$jobs" = infinite ]; then
    exec "$@" -j "$(nproc)"
  else
    >&2 echo "Cannot run -j $jobs without jobserver"
    exit 1
  fi
elif ! [ "$jobs" ]; then
  >&2 echo "Missing -j info for jobserver use"
  exit 1
elif [ "$mode" = fifo ]; then
  # $((jobs - 1)): there is an implicit job for the current process (IIUC)
  # (-j 1 doesn't have a jobserver)
  # TODO give back tokens if we get interrupted (otherwise make may complain?)
  read -rn $((jobs - 1)) chars < "$server_in"
  ( set -x; "$@" -j "$jobs" )
  res=$?
  printf '%s' "$chars" > "$server_out"
  exit $res
elif [ "$mode" = pipes ]; then
  read -rn $((jobs - 1)) chars <& "$server_in"
  ( set -x; "$@" -j "$jobs" )
  res=$?
  printf '%s' "$chars" >& "$server_out"
  exit $res
else
  >&2 assert false
  exit 1
fi
