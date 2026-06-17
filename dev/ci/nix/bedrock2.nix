{}:
{
  configure = "git submodule update --init --recursive";
  clean = "(cd compiler && make clean); (cd bedrock2 && make clean)";
}
