#!/usr/bin/env bash

# This is the list of repositories used by the CI scripts, unless overridden
# by a call to the "overlay" function in ci-common

declare -a projects # the list of project repos that can be be overlayed

# checks if the given argument is a known project
function is_in_projects {
    for x in "${projects[@]}"; do
      if [ "$1" = "$x" ]; then return 0; fi;
    done
    return 1
}

# project <name> <giturl> <ref> [<archiveurl>]
#   [<archiveurl>] defaults to <giturl>/archive on github.com
#   and <giturl>/-/archive on gitlab
function project {

  local var_ref=${1}_CI_REF
  local var_giturl=${1}_CI_GITURL
  local var_archiveurl=${1}_CI_ARCHIVEURL
  local giturl=$2
  local ref=$3
  local archiveurl=$4
  case $giturl in
    *github.com*) archiveurl=${archiveurl:-$giturl/archive} ;;
    *gitlab*) archiveurl=${archiveurl:-$giturl/-/archive} ;;
  esac

  # register the project in the list of projects
  projects[${#projects[*]}]=$1

  # bash idiom for setting a variable if not already set
  : "${!var_ref:=$ref}"
  : "${!var_giturl:=$giturl}"
  : "${!var_archiveurl:=$archiveurl}"

}

# subproject <name> <parent project> <submodulefolder> <submodule giturl> <submodule branch>
# In the case of nested submodules, each subproject should be declared
# a subproject of its immediate parent, to ensure overlays are applied
# in the right order
function subproject {
  local var_parent_project=${1}_CI_PARENT_PROJECT
  local var_submodule_folder=${1}_CI_SUBMODULE_FOLDER
  local var_submodule_giturl=${1}_CI_SUBMODULE_GITURL
  local var_submodule_branch=${1}_CI_SUBMODULE_BRANCH
  local parent_project=$2
  local submodule_folder=$3
  local submodule_giturl=$4
  local submodule_branch=$5

  # register the project in the list of projects
  projects[${#projects[*]}]=$1

  : "${!var_parent_project:=$parent_project}"
  : "${!var_submodule_folder:=$submodule_folder}"
  : "${!var_submodule_giturl:=$submodule_giturl}"
  : "${!var_submodule_branch:=$submodule_branch}"
}

########################################################################
# Micromega
########################################################################
project micromega 'https://github.com/rocq-community/micromega-plugin' '24710e3932e88917074b8d9a1c37cbaf585965e2'
# Contact @proux01 on github

########################################################################
# MathComp
########################################################################
project mathcomp 'https://github.com/math-comp/math-comp' '705783bd45718a499393b754e0edba92676e16a8'
# Contact @CohenCyril, @proux01 on github

project fourcolor 'https://github.com/math-comp/fourcolor' 'f2fcc837b817632f334f9c7d7fbb0195ad4ba4e2'
# Contact @proux01 on github

project oddorder 'https://github.com/math-comp/odd-order' '6afa795b9018c64ab5c7cd2f9b3c9ab5dd45d93f'
# Contact @gares, @proux01 on github

project mczify 'https://github.com/math-comp/mczify' 'f11611e6f17c9152b05ad67aba26cc5c35b14fa0'
# Contact @pi8027 on github

project finmap 'https://github.com/math-comp/finmap' '53239c7997b1143592d7814ec51a0e3404844b54'
# Contact @CohenCyril on github

project bigenough 'https://github.com/math-comp/bigenough' '764f47d3d9d0630a0e0a341d5fb9b51ad99ff2a1'
# Contact @CohenCyril on github

project analysis 'https://github.com/math-comp/analysis' 'e340551bbd7b65fc2ed7b15c2182b6c660e8ad6d'
# Contact @affeldt-aist, @CohenCyril on github

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '42a789be86dc71145bebe84225a8f292a3b084ae'
# Contact @benediktahrens, @m-lindgren, @nmvdw, @rmatthes on github

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' 'afff890feb05adfae6362344ba8b088c40059706'
# Contact @Janno, @mattam82 on github

project mtac2 'https://github.com/Mtac2/Mtac2' 'b229396fbfe474c0b9c5a7732dd5988454cb291a'
# Contact @Janno on github

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' '257619f0479a90ed97a53e2edd1425002c20ea95'
# Contact @Lysxia and @spitters on github

project corn 'https://github.com/coq-community/corn' 'ada7c0b497ff15dd67cf7932c6f20e143a2aee2f'
# Contact @Lysxia and @spitters on github

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris and
# iris_examples repos respectively. So just getting a fix landed in stdpp or
# Iris is not enough. Ping @RalfJung and @robbertkrebbers if you need the
# versions of stdpp or Iris to be bumped.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""
# Contact @RalfJung, @robbertkrebbers on github

project iris "https://gitlab.mpi-sws.org/iris/iris" ""
# Contact @RalfJung, @robbertkrebbers on github

project autosubst 'https://github.com/coq-community/autosubst' '50dfe574c0bd415925eea47c1f5b1a533aa85269'
# Contact @RalfJung on github

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' 'd02cddf760f038f603360d74895f8347f053ac37'
# Contact @RalfJung, @robbertkrebbers on github

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' 'a030184c0bfc9d61f3bcd33c67660b800e106427'
# Contact @Alizter, @jdchristensen on github

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '810ee0b644022104de2dae3a4f397c08c9681b9d'
# Contact @lukaszcz on github

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '8ca92d399c29a03d73379e0ec468340621ffdfe5'
# Contact @silene on github

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' '87eab829c09c3719f09d4afee80c91a0ec2adc51'
# Contact @JasonGross on github

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' 'd0887fa516ffcb6c1cb7ba11215837640dd8e33a'
# Contact @JasonGross on github

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' 'a31242c6efeb77a4874ddbac40eeeb8f1acb1280'
# Contact @silene on github

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' '5d00ef03b12767dfef104374611c3935ec3edae2'
# Contact @xavierleroy on github

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' 'cbee87efb4bee2b588f8321e16b4cb7664d5cf60'
# Contact @andrew-appel on github

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' 'bed456b1068058c0f80e559a845e0e40aad5dc73'
# Contact @JasonGross on github

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' '87174d638f5d86b710e5635ee4915118649bce1e'
# Contact @JasonGross on github

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' 'fef9ba2b6b710e0dee3cf36ade3a021b14f97ac0'
# Contact @JasonGross on github

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' '7ba6bace044c422f14cf3a18a3be1b2115066b50'
# Contact @andres-erbsen, @JasonGross on github

# bedrock2, coqutil, rupicola
# fiat-crypto is not guaranteed to build with the latest version of
# bedrock2, so we use the pinned version of bedrock2 for fiat-crypto
# overlays do not have to follow suite
subproject rupicola fiat_crypto "rupicola" "https://github.com/mit-plv/rupicola" "master"
subproject bedrock2 rupicola "bedrock2" "https://github.com/mit-plv/bedrock2" "master"
subproject coqutil bedrock2 "deps/coqutil" "https://github.com/mit-plv/coqutil" "master"
# Contact @samuelgruetter, @andres-erbsen on github

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/coq-community/coq-dpdgraph' '86433889a23298cb946175df9578434ec20990a2'
# Contact @Karmaki, @ybertot on github

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' '7ed50c447ddd9ea50013bc999a18267e72687f2c'
# Contact @fblanqui on github

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' '36cd7009759b797b9b248ca91959e11494e89a4a'
# Contact @erikmd, @proux01 on github

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' 'd2ae1dd36bdebcc362e155933e54fe4921975e37'
# Contact @thery on github

########################################################################
# Coinduction
########################################################################
project coinduction 'https://github.com/damien-pous/coinduction' '81ecd5f1ffa3e46b696d9461c88ad6ca9be5cfc7'
# Contact @damien-pous on github

########################################################################
# rocq-lsp
########################################################################
project rocq_lsp 'https://github.com/rocq-community/rocq-lsp' '2ac2a159f551859aa266b15602362430e30c29f5'
# Contact @SkySkimmer on github

########################################################################
# Equations
########################################################################
project equations 'https://github.com/rocq-prover/equations' 'd562d8c413f4b0d2a837ef742d08fa59d14107e6'
# Contact @mattam82 on github

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' '696fd9dfa092f304a046ea66303d7e916608ba2b'
# Contact @gares on github

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' '4d8a9399575f6a8a89e3fa4c2591f21070e40250'
# Contact @CohenCyril, @gares on github

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' '08ecd3ae6e73ff6e62b47fd62f5c57e4ec4fb42d'
# Contact @JasonGross on github

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' '4f55ee22b254c545a054e289712a6d8128326f28'
# Contact @aleksnanevski, @clayrat on github

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' 'ddd03d257f6b85a93bfaa0ed4d03658e0ddf5075'
# Contact @liyishuai on github

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' 'd035c0a85f0bde4ad56c31a9fa9ef3cb5e8d0f18'
# Contact @Lysxia, @liyishuai on github

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' '3d4d6c0e9f72172a9f0b26db61c5496ec8e0f568'
# Contact @lemonidas, @Lysxia, @liyishuai on github

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' '289bfdea1e80dbc22ecbc00bae6d5e667ba53070'
# Contact @liyishuai, @JasonGross on github

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib 'https://gitlab.inria.fr/fpottier/menhir' '054f73ca06936f550eec046368eee7c696acc417'
# Contact @fpottier, @jhjourdan on github

########################################################################
# coq-neural-net-interp
########################################################################
project neural_net_interp 'https://github.com/JasonGross/neural-net-coq-interp' '98a25401653c739bfddc5a70d34662df7af8148d'
# Contact @JasonGross on github

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' '09523f9910891dcc2072f2b87fee658a62feb484'
# Contact @palmskog on github

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' 'd0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf'
# Contact @damhiya on github

########################################################################
# coq-itree
########################################################################
project itree 'https://github.com/DeepSpec/InteractionTrees' '68b3568d3f0f48c057192c58c8db88ef4412747a'
# Contact @Lysxia on github

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' 'eba83b1cc03bb1ef4dc4384129a975e4286736db'
# Contact @ppedrot on github

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' '2d2af3631929399bbac56f57b3e15302d8697e1c'
# Contact @damien-pous on github

########################################################################
# Stdlib
########################################################################
project stdlib 'https://github.com/coq/stdlib' 'b89635f66d5d5fe3c91a5755b389a30846411888'
# Contact TODO on github

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' '76179234a3b1e43bf7f6a9493024c9aa42bf98f6'
# Contact @tchajed on github

########################################################################
# ATBR
########################################################################
project atbr 'https://github.com/coq-community/atbr' '1806f95dd68b953312cbee44224ea1e96de9f35f'
# Contact @palmskog, @tchajed on github

########################################################################
# metarocq
########################################################################
project metarocq 'https://github.com/MetaRocq/metarocq' '9242c14bc377611a56d45283977ea754fd499c47'
# Contact @mattam82, @yforster on github

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' '253024419a06b8bffe0aad27f8d4fcac4b6a9d17'
# Contact @bcpierce00, @liyishuai on github

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' 'f513d17d3cb93067393a79b208330b06d9fbc22b'
# Contact @whonore on github

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' '60676c5ca45331963b8f7cdd9ed2aecf5dcfd609'
# Contact @arthuraa on github

########################################################################
# VsRocq
########################################################################
project vsrocq 'https://github.com/rocq-prover/vsrocq' '26e22afe9219114644b3452a1e3b43e500bdc6cc'
# Contact @rtetley, @gares on github

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' 'a98ea19d495b2fc8288d4d2774b5b908723713d0'
# Contact @jwiegley on github

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' 'cda354a508a8ea4e415f4ddc99976e942ff8dace'
# Contact @fajb on github

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word 'https://github.com/jasmin-lang/coqword' '3ba8484ae779a2178ea3c6a470f102a0dd57a8a9'
# Contact @vbgl, @strub on github

########################################################################
# Jasmin
########################################################################
project jasmin 'https://github.com/jasmin-lang/jasmin' '1c419e5cab1aee15d2e11be883a7f290483f6d25'
# Contact @vbgl, @bgregoir on github

########################################################################
# Lean Importer
########################################################################
project lean_importer 'https://github.com/coq-community/rocq-lean-import' '38fb4791bc7a3bc49995526448778c6e5555aaf1'
# Contact @SkySkimmer on github

########################################################################
# SMTCoq
########################################################################
project smtcoq 'https://github.com/smtcoq/smtcoq' 'e7e54ca0180d233d98c54a74e0e8d13356887148'
# Contact @ckeller on github

########################################################################
# Stalmarck
########################################################################
project stalmarck 'https://github.com/coq-community/stalmarck' '698fb18415d10bfef07af3a3935acf551a829322'
# Contact @palmskog on github

########################################################################
# Tactician
########################################################################
project tactician 'https://github.com/coq-tactician/coq-tactician' '6e05582a5c9e595f4108df20678e2e316faa426c'
# Contact @LasseBlaauwbroek on github

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler 'https://github.com/SkySkimmer/coq-ltac2-compiler' 'd338d017cc68ff8e5423a0d1b730a99564e2c096'
# Contact @SkySkimmer on github

########################################################################
# Waterproof
########################################################################
project waterproof 'https://github.com/impermeable/coq-waterproof' 'f49b8305b74eeddc039282de6f610b34ca941713'
# Contact @jellooo038, @jim-portegies on github

########################################################################
# Autosubst (2) OCaml
########################################################################
project autosubst_ocaml 'https://github.com/uds-psl/autosubst-ocaml' '0f4b164b25ef7bf99ba60b737c0852655cc42309'
# Contact @yforster on github

########################################################################
# Trakt
########################################################################
project trakt 'https://github.com/rocq-trakt/trakt' '664ecad1830d9885b645f33b9e511d113f42a34f'
# Contact @ckeller, @lafeychine on github

########################################################################
# MLtac2
########################################################################
project mltac2 'https://github.com/epfl-systemf/mltac2' '86572463f5d09995c6f0d6bd180c1075f020eb82'
# Contact @dhalilov on github
