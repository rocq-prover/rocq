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
# MathComp
########################################################################
project mathcomp 'https://github.com/math-comp/math-comp' '1378d07ead40985f5251ae92bbe3eb7905aa37b4'
# Contact @CohenCyril, @proux01 on github

project fourcolor 'https://github.com/math-comp/fourcolor' '9990abd7a15f80916c14367ac6dec947a836e60e'
# Contact @ybertot, @proux01 on github

project oddorder 'https://github.com/math-comp/odd-order' 'e170ac09942df7d4f2b2bab364624dd073619075'
# Contact @gares, @proux01 on github

project mczify 'https://github.com/math-comp/mczify' '96dfac88f969ded4b4db5b3e2805ce9efaa0bcaa'
# Contact @pi8027 on github

project algebra_tactics 'https://github.com/math-comp/algebra-tactics' '88aab35361541ddf1ba199438122f3a91469e27e'
# Contact @pi8027, @proux01 on github

project finmap 'https://github.com/math-comp/finmap' 'c0cf3df180b7279a7e6ac9367bd5a7aa66af56a7'
# Contact @CohenCyril on github

project bigenough 'https://github.com/math-comp/bigenough' 'eed6cf38d6d20e2b20d29b3778dacbe9f85394c3'
# Contact @CohenCyril on github

project analysis 'https://github.com/math-comp/analysis' '4d9168b8779c870d49fe7d9071c7d755ab1081a2'
# Contact @affeldt-aist, @CohenCyril on github

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '7563807290859c82b029534d9187318456c1e0f7'
# Contact @benediktahrens, @m-lindgren, @nmvdw, @rmatthes on github

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' 'd52374ca86e3885197f114555e742420fa9bbe94'
# Contact @beta-ziliani, @Janno, @mattam82 on github

project mtac2 'https://github.com/Mtac2/Mtac2' 'fe8b6049835caa793436e277a64ee7e4910f7b04'
# Contact @beta-ziliani, @Janno, @mattam82 on github

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' '257619f0479a90ed97a53e2edd1425002c20ea95'
# Contact @Lysxia and @spitters on github

project corn 'https://github.com/coq-community/corn' '225384e459d911441f4b473419d00c2fb2fa6eab'
# Contact @Lysxia and @spitters on github

########################################################################
# Iris
########################################################################

# NB: stdpp and Iris refs are gotten from the opam files in the Iris and
# iris_examples repos respectively. So just getting a fix landed in stdpp or
# Iris is not enough. Ping @RalfJung and @robbertkrebbers if you need the
# versions of stdpp or Iris to be bumped. Perennial also has its own pinned
# versions of stdpp and Iris; ping @tchajed and @zeldovich to get that bumped.
project stdpp "https://gitlab.mpi-sws.org/iris/stdpp" ""
# Contact @RalfJung, @robbertkrebbers on github

project iris "https://gitlab.mpi-sws.org/iris/iris" ""
# Contact @RalfJung, @robbertkrebbers on github

project autosubst 'https://github.com/coq-community/autosubst' '50dfe574c0bd415925eea47c1f5b1a533aa85269'
# Contact @RalfJung, @co-dan on github

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' '4a2b79da62a386895afd6586c77998182f262704'
# Contact @RalfJung, @robbertkrebbers on github

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' '4e1662f5ea7a10b31b794adcee1392671db77b1c'
# Contact @Alizter, @jdchristensen on github

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '1d581299c2a85af175b53bd35370ea074af922ec'
# Contact @lukaszcz on github

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' '54cadd27b64daafa1b94a97dba6011ae46048113'
# Contact @silene on github

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' '940baa2bc2753ba65d2c9d0918618aa50721902c'
# Contact @JasonGross on github

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' '1b4ec4a46c9c0737da361aae5b9b812f99a9cb5d'
# Contact @JasonGross on github

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' '22314576d5d067fa49f5c9cced0a94d409f8cb65'
# Contact @silene on github

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' '821abd5f3d7eaf5a430c4d163726f2743a23cb79'
# Contact @xavierleroy on github

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' 'bde826e50ab2a6ca67c38de2ab689ffd6920fef2'
# Contact @andrew-appel on github

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' '64d06b2be33c4d4d1bdeea4854d4bb04d66a162d'
# Contact @andres-erbsen on github

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' 'dd37fb28ed7f01a3b7edc0675a86b95dd3eb1545'
# Contact @JasonGross on github

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' 'c171d6d1b31b2282c7d2623e93e8c3791cf40508'
# Contact @JasonGross on github

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '09f4c780b4e7f1a6a5b71df4f169c0c5c9378d5d'
# Contact @JasonGross on github

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' 'fc8ce4b3ced2e8a24773b708666a74d132a8425e'
# Contact @andres-erbsen, @JasonGross on github

# bedrock2, coqutil, rupicola, kami, riscv_coq
# fiat-crypto is not guaranteed to build with the latest version of
# bedrock2, so we use the pinned version of bedrock2 for fiat-crypto
# overlays do not have to follow suite
subproject rupicola fiat_crypto "rupicola" "https://github.com/mit-plv/rupicola" "master"
subproject bedrock2 rupicola "bedrock2" "https://github.com/mit-plv/bedrock2" "master"
subproject coqutil bedrock2 "deps/coqutil" "https://github.com/mit-plv/coqutil" "master"
subproject kami bedrock2 "deps/kami" "https://github.com/mit-plv/kami" "rv32i"
subproject riscv_coq bedrock2 "deps/riscv-coq" "https://github.com/mit-plv/riscv-coq" "master"
# Contact @samuelgruetter, @andres-erbsen on github

########################################################################
# coq_dpdgraph
########################################################################
project coq_dpdgraph 'https://github.com/coq-community/coq-dpdgraph' '7a0fba21287dd8889c55e6611f8ba219d012b81b'
# Contact @Karmaki, @ybertot on github

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' '42d00eb8030fabdedf2d8eee4010fe0f89bd544a'
# Contact @fblanqui on github

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' 'fd53b3b2f0a0d7c24c8363fbd4570a451198ded7'
# Contact @charguer on github

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' '30a45625546da0a88db8689a8009d580aa3f557f'
# Contact @erikmd, @proux01 on github

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' '589b9761e4efcb37277d5548ece6174255c9ac83'
# Contact @thery on github

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' '032537e726ad2b235a16162e83357f054a3039be'
# Contact @JasonGross, @samuelgruetter on github

########################################################################
# Coinduction
########################################################################
project coinduction 'https://github.com/damien-pous/coinduction' '9502ae09e9f87518330f37c08bc19a8c452dcd91'
# Contact @damien-pous on github

########################################################################
# coq-lsp
########################################################################
project coq_lsp 'https://github.com/ejgallego/coq-lsp' 'bd6fb39fc0ac51330c3543ef727d7fa3c81d7b96'
# Contact @ejgallego on github

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' '757662b9c875d7169a07b861d48e82157520ab1a'
# Contact @mattam82 on github

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' '1ab7fcc7dc5eae1e25f4a61ebd4d6cf97dbbbfd8'
# Contact @gares on github

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' '2156a76d8a59d2b8a3571fc6c02e3b44010ab7d7'
# Contact @CohenCyril, @gares on github

########################################################################
# Engine-Bench
########################################################################
project engine_bench 'https://github.com/mit-plv/engine-bench' '08ecd3ae6e73ff6e62b47fd62f5c57e4ec4fb42d'
# Contact @JasonGross on github

########################################################################
# fcsl-pcm
########################################################################
project fcsl_pcm 'https://github.com/imdea-software/fcsl-pcm' '69c244e93e6790100065eb59a307adba6d1775a8'
# Contact @aleksnanevski, @clayrat on github

########################################################################
# ext-lib
########################################################################
project ext_lib 'https://github.com/coq-community/coq-ext-lib' '07d35df4c9e7ae3bf390e553822fb9ddbd943dd2'
# Contact @gmalecha, @liyishuai on github

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' 'f6cadf769e94ceca204ca9c54282df07714422a7'
# Contact @Lysxia, @liyishuai on github

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' '4a3a725dfca7dccbfc3ebdce548a41ccd78e0507'
# Contact @lemonidas, @Lysxia, @liyishuai on github

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' '29541ef53bfbd75f055ebade16cf8ea60f9528c4'
# Contact @liyishuai, @JasonGross on github

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib 'https://gitlab.inria.fr/fpottier/menhir' '276ae1d97e6c6e5154ff9f6f3ca7b4783e6d1218'
# Contact @fpottier, @jhjourdan on github

########################################################################
# coq-neural-net-interp
########################################################################
project neural_net_interp 'https://github.com/JasonGross/neural-net-coq-interp' '5b496f9ae337e0fca44fcc20df450dc828bab16c'
# Contact @JasonGross on github

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' '4f796a7b0ee88330162727fc6ea988a7e0ea46e3'
# Contact @palmskog on github

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' 'd0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf'
# Contact @minkiminki on github

########################################################################
# coq-itree
########################################################################
project itree 'https://github.com/DeepSpec/InteractionTrees' 'bd356ec0d2ea1cf13ed08b129967027f0f81b882'
# Contact @Lysxia on github

########################################################################
# coq-itree_io
########################################################################
project itree_io 'https://github.com/Lysxia/coq-itree-io' 'af0326793a19f142eba800dba6044143b108ceaa'
# Contact @Lysxia, @liyishuai on github

########################################################################
# coq-ceres
########################################################################
project ceres 'https://github.com/Lysxia/coq-ceres' 'f61b24d48222db0100de19f88c19151a3aeb826f'
# Contact @Lysxia on github

########################################################################
# coq-parsec
########################################################################
project parsec 'https://github.com/liyishuai/coq-parsec' '3feabc998705927ca2d2f9249a21a6e15c394162'
# Contact @liyishuai on github

########################################################################
# coq-json
########################################################################
project json 'https://github.com/liyishuai/coq-json' '60c1994f2005e01efcfc3d935702748e86dafe2b'
# Contact @liyishuai on github

########################################################################
# coq-async-test
########################################################################
project async_test 'https://github.com/liyishuai/coq-async-test' '0637b95ae52060d8a808261ca97890d03c9a4503'
# Contact @liyishuai on github

########################################################################
# coq-http
########################################################################
project http 'https://github.com/liyishuai/coq-http' 'ab051acc4471876b45ed462f5763d2132204613a'
# Contact @liyishuai on github

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' 'f8026210f37faf6c4031de24ada9fdded29d67e5'
# Contact @ppedrot on github

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' 'ba3db5783060d9e25d1db5e377fc9d71338a5160'
# Contact @damien-pous on github

########################################################################
# StructTact + InfSeqExt + Cheerios + Verdi + Verdi Raft
########################################################################
project struct_tact 'https://github.com/uwplse/StructTact' '97268e11564c8fe59aa72b062478458d7aa53e9d'
# Contact @palmskog on github

project inf_seq_ext 'https://github.com/DistributedComponents/InfSeqExt' '601e89ec019501c48c27fcfc14b9a3c70456e408'
# Contact @palmskog on github

project cheerios 'https://github.com/uwplse/cheerios' '5c9318c269f9cae1c1c6583a44405969ac0be0dd'
# Contact @palmskog on github

project verdi 'https://github.com/uwplse/verdi' '20a587e075c6b3da3f8172ff0095c756059cc308'
# Contact @palmskog on github

project verdi_raft 'https://github.com/uwplse/verdi-raft' 'a3375e867326a82225e724cc1a7b4758b029376f'
# Contact @palmskog on github

########################################################################
# Stdlib
########################################################################
project stdlib 'https://github.com/coq/stdlib' 'd722e595fb5a520717fdca676fe1545c4fa35626'
# Contact TODO on github

########################################################################
# argosy
########################################################################
project argosy 'https://github.com/mit-pdos/argosy' '9fa42b78b7f9b7b989fb3434dfbfec4abcfcbff8'
# Contact @tchajed on github

########################################################################
# ATBR
########################################################################
project atbr 'https://github.com/coq-community/atbr' '47ac8fb6bf244d9a4049e04c01e561191490f543'
# Contact @palmskog, @tchajed on github

########################################################################
# perennial
########################################################################
project perennial 'https://github.com/mit-pdos/perennial' '394e461a6d0815c66656d28d4749adcde950cab7'
# Contact @upamanyus, @tchajed on github
# PRs to fix Perennial failures should be submitted against the Perennial
# `master` branch. `coq/tested` is automatically updated every night to the
# `master` branch if CI on `master` is green. This is to avoid breaking Coq CI
# when Perennial CI breaks.

########################################################################
# metarocq
########################################################################
project metarocq 'https://github.com/MetaRocq/metarocq' 'e8f8078e756cc378b830eb5a8e4637df43d481af'
# Contact @mattam82, @yforster on github

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' '5e863a9f92e515a0e11641f28077a64919f8482e'
# Contact @bcpierce00, @liyishuai on github

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' 'a25018e4f371016aefea267038ac5d083b615da9'
# Contact @whonore on github

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' '1eac44362d895d84c37ac2db308caa7833035f2a'
# Contact @arthuraa on github

########################################################################
# VsRocq
########################################################################
project vsrocq 'https://github.com/rocq-prover/vsrocq' 'cf0e9c3b327e155b391df40ed84fd0270dadfffb'
# Contact @rtetley, @gares on github

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' '7da7ce8777b721b98d28027e5c475a75790181ed'
# Contact @jwiegley on github

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' '8190a58b730b0439b55d05d7238435da8224c22f'
# Contact @fajb on github

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word 'https://github.com/jasmin-lang/coqword' '95f0a6a0a290d6b78ee39af7053a93cec5327060'
# Contact @vbgl, @strub on github

########################################################################
# Jasmin
########################################################################
project jasmin 'https://github.com/jasmin-lang/jasmin' 'a60227fb7a9e60f8bcc15eb30ea5cf2abadc2496'
# Contact @vbgl, @bgregoir on github

########################################################################
# Lean Importer
########################################################################
project lean_importer 'https://github.com/coq-community/rocq-lean-import' 'b8291b9dae4f5ed780112e95eea484e435199b46'
# Contact @SkySkimmer on github

########################################################################
# SMTCoq
########################################################################
project smtcoq 'https://github.com/smtcoq/smtcoq' 'cff0a8cdb7c73b6c59965a749a4304f3c4ac01bf'
# Contact @ckeller on github

project smtcoq_trakt 'https://github.com/smtcoq/smtcoq' '9392f7446a174b770110445c155a07b183cdca3d'
# Contact @ckeller on github

########################################################################
# Stalmarck
########################################################################
project stalmarck 'https://github.com/coq-community/stalmarck' 'd32acd3c477c57b48dd92bdd96d53fb8fa628512'
# Contact @palmskog on github

########################################################################
# Tactician
########################################################################
project tactician 'https://github.com/coq-tactician/coq-tactician' '6750c1d7d58b2ca3057cb23f6e1d19f5674cfb08'
# Contact @LasseBlaauwbroek on github

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler 'https://github.com/SkySkimmer/coq-ltac2-compiler' '0401985b54ce426f4901f35ff6e827685927030a'
# Contact @SkySkimmer on github

########################################################################
# Waterproof
########################################################################
project waterproof 'https://github.com/impermeable/coq-waterproof' '99ad6ff78fa700c84ba0cb1d1bda27d8e0f11e1a'
# Contact @jellooo038, @jim-portegies on github

########################################################################
# Autosubst (2) OCaml
########################################################################
project autosubst_ocaml 'https://github.com/uds-psl/autosubst-ocaml' '772acb2248738fd4bc51b122c454ccb3f01cdeec'
# Contact @yforster on github

########################################################################
# Trakt
########################################################################
project trakt 'https://github.com/ecranceMERCE/trakt' 'bd49a3077b8aa0522368c84dae349e5006b36f0b'
# Contact @ckeller on github
