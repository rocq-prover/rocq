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
project mathcomp 'https://github.com/math-comp/math-comp' '0c8979a7a24cb71d5e986a66548d56d57f30762d'
# Contact @CohenCyril, @proux01 on github

project fourcolor 'https://github.com/math-comp/fourcolor' 'dff565790a6aad4d64373046e723c4163c85b5f9'
# Contact @ybertot, @proux01 on github

project oddorder 'https://github.com/math-comp/odd-order' '0ae93b443d14becaab819d1de490df88d5fb9d19'
# Contact @gares, @proux01 on github

project mczify 'https://github.com/math-comp/mczify' 'd4ec06f83fdadaac59734557803094a3cd63f3d0'
# Contact @pi8027 on github

project algebra_tactics 'https://github.com/math-comp/algebra-tactics' '9d17d45cadc4d0a3ca971c8b4e13bf5db2bff26a'
# Contact @pi8027, @proux01 on github

project finmap 'https://github.com/math-comp/finmap' '054881ad521ab62d9fd3457ba541a3d4f3734147'
# Contact @CohenCyril on github

project bigenough 'https://github.com/math-comp/bigenough' '596834243018593f1855201d2ff7228d09f1afde'
# Contact @CohenCyril on github

project analysis 'https://github.com/math-comp/analysis' '6e62b37d02cb8fd357a054a91c160e07671a7d40'
# Contact @affeldt-aist, @CohenCyril on github

########################################################################
# UniMath
########################################################################
project unimath 'https://github.com/UniMath/UniMath' '5941f44e3c13d2ac385f5a8b9b486c0088dd3f46'
# Contact @benediktahrens, @m-lindgren, @nmvdw, @rmatthes on github

########################################################################
# Unicoq + Mtac2
########################################################################
project unicoq 'https://github.com/unicoq/unicoq' '28ec18aef35877829535316fc09825a25be8edf1'
# Contact @beta-ziliani, @Janno, @mattam82 on github

project mtac2 'https://github.com/Mtac2/Mtac2' 'bcbefa79406fc113f878eb5f89758de241d81433'
# Contact @beta-ziliani, @Janno, @mattam82 on github

########################################################################
# Mathclasses + Corn
########################################################################
project math_classes 'https://github.com/coq-community/math-classes' '40de430909768abae6ed34be818ecfad809342e3'
# Contact @Lysxia and @spitters on github

project corn 'https://github.com/coq-community/corn' 'a75b14fad50313d615881713d4703e6c9cd6e111'
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

project iris_examples 'https://gitlab.mpi-sws.org/iris/examples' 'dc20f8669b503db47030223dcf465b26577cb34a'
# Contact @RalfJung, @robbertkrebbers on github

########################################################################
# HoTT
########################################################################
project hott 'https://github.com/HoTT/HoTT' 'de76def86967866f7ca9cc3f3c17b40f2ab16bb1'
# Contact @Alizter, @jdchristensen on github

########################################################################
# CoqHammer
########################################################################
project coqhammer 'https://github.com/lukaszcz/coqhammer' '8649603dcbac5d92eaf1319a6b7cdfc65cdd804b'
# Contact @lukaszcz on github

########################################################################
# Flocq
########################################################################
project flocq 'https://gitlab.inria.fr/flocq/flocq' 'd0875fdba19cb4689cf1de6164d0adfd6b5e9d75'
# Contact @silene on github

########################################################################
# coq-performance-tests
########################################################################
project coq_performance_tests 'https://github.com/coq-community/coq-performance-tests' '940baa2bc2753ba65d2c9d0918618aa50721902c'
# Contact @JasonGross on github

########################################################################
# coq-tools
########################################################################
project coq_tools 'https://github.com/JasonGross/coq-tools' '2d9bb862ec97979ad25cb1a000a6c7c2f38928fd'
# Contact @JasonGross on github

########################################################################
# Coquelicot
########################################################################
project coquelicot 'https://gitlab.inria.fr/coquelicot/coquelicot' 'dbcd5010d1770eb8cd3bf100a0a2f51acaa6b661'
# Contact @silene on github

########################################################################
# CompCert
########################################################################
project compcert 'https://github.com/AbsInt/CompCert' '76f7feabd0d549a12ca139d6af953c4c30e814cc'
# Contact @xavierleroy on github

########################################################################
# VST
########################################################################
project vst 'https://github.com/PrincetonUniversity/VST' '127aa7346e1dbd8da066a2a11c540ee6768a485b'
# Contact @andrew-appel on github

########################################################################
# cross-crypto
########################################################################
project cross_crypto 'https://github.com/mit-plv/cross-crypto' 'a99fefcf4310264c178cd53d731af97c0f1c82f9'
# Contact @andres-erbsen on github

########################################################################
# rewriter
########################################################################
project rewriter 'https://github.com/mit-plv/rewriter' '9496defb8b236f442d11372f6e0b5e48aa38acfc'
# Contact @JasonGross on github

########################################################################
# fiat_parsers
########################################################################
project fiat_parsers 'https://github.com/mit-plv/fiat' 'd6f2f59fa6a6ebbb5cff818bab8c3f1f16fea1bd'
# Contact @JasonGross on github

########################################################################
# fiat_crypto_legacy
########################################################################
project fiat_crypto_legacy 'https://github.com/mit-plv/fiat-crypto' '54d90a996f4155d985df3fd126c3c242e35342b9'
# Contact @JasonGross on github

########################################################################
# fiat_crypto
########################################################################
project fiat_crypto 'https://github.com/mit-plv/fiat-crypto' '9eb8af1324ad20332042987900fecbb33b048803'
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
project coq_dpdgraph 'https://github.com/coq-community/coq-dpdgraph' '7817def06d4e3abc2e54a2600cf6e29d63d58b8a'
# Contact @Karmaki, @ybertot on github

########################################################################
# CoLoR
########################################################################
project color 'https://github.com/fblanqui/color' '7ef5cf16c45421283445f999787886479a3a8746'
# Contact @fblanqui on github

########################################################################
# TLC
########################################################################
project tlc 'https://github.com/charguer/tlc' '51be762eedec72788490f1fd222eb8b0d82b8bea'
# Contact @charguer on github

########################################################################
# Bignums
########################################################################
project bignums 'https://github.com/coq/bignums' '9f9855536bd4167af6986f826819e32354b7da22'
# Contact @erikmd, @proux01 on github

########################################################################
# coqprime
########################################################################
project coqprime 'https://github.com/thery/coqprime' '45c784d122ed84194cd977c8453c98acd529193f'
# Contact @thery on github

########################################################################
# bbv
########################################################################
project bbv 'https://github.com/mit-plv/bbv' 'c53d5b95c70839ae8e947010d85503bd1ada1120'
# Contact @JasonGross, @samuelgruetter on github

########################################################################
# Coinduction
########################################################################
project coinduction 'https://github.com/damien-pous/coinduction' '823b424778feff8fbd9759bc3a044435ea4902d1'
# Contact @damien-pous on github

########################################################################
# coq-lsp
########################################################################
project coq_lsp 'https://github.com/ejgallego/coq-lsp' 'a46cd5f97e072ccb2977cd8efa152076a14c52fc'
# Contact @ejgallego on github

########################################################################
# Equations
########################################################################
project equations 'https://github.com/mattam82/Coq-Equations' '2137c8e7081f2d47ab903de0cc09fd6a05bfab01'
# Contact @mattam82 on github

########################################################################
# Elpi + Hierarchy Builder
########################################################################
project elpi 'https://github.com/LPCIC/coq-elpi' 'acf29a35983328e062843913b48c36f2057fb59b'
# Contact @gares on github

project hierarchy_builder 'https://github.com/math-comp/hierarchy-builder' '4b6a76fb6802a770dd929a9dd7e8e03c3a47f73e'
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
project ext_lib 'https://github.com/coq-community/coq-ext-lib' 'b27e806daf39a8f1cfc7ced09c1af44d390af4a6'
# Contact @gmalecha, @liyishuai on github

########################################################################
# simple-io
########################################################################
project simple_io 'https://github.com/Lysxia/coq-simple-io' '98d038bba0a481deb1bd03c3e05c5abd5d48be73'
# Contact @Lysxia, @liyishuai on github

########################################################################
# quickchick
########################################################################
project quickchick 'https://github.com/QuickChick/QuickChick' '29ef41e628319e4d39dea377ffa49dd541705869'
# Contact @lemonidas, @Lysxia, @liyishuai on github

########################################################################
# reduction-effects
########################################################################
project reduction_effects 'https://github.com/coq-community/reduction-effects' '2e6590125885906ec0c5157b114d2afba18ab9c8'
# Contact @liyishuai, @JasonGross on github

########################################################################
# menhirlib
########################################################################
# Note: menhirlib is now in subfolder coq-menhirlib of menhir
project menhirlib 'https://gitlab.inria.fr/fpottier/menhir' 'ac08b55d316e6814d4bda1c995e7e0ed008c0e76'
# Contact @fpottier, @jhjourdan on github

########################################################################
# coq-neural-net-interp
########################################################################
project neural_net_interp 'https://github.com/JasonGross/neural-net-coq-interp' '7e0c38173eb9147bde15e17ac43583df96289465'
# Contact @JasonGross on github

########################################################################
# aac_tactics
########################################################################
project aac_tactics 'https://github.com/coq-community/aac-tactics' 'e68d028cef838f5821d184fed0caea9eedd5538a'
# Contact @palmskog on github

########################################################################
# paco
########################################################################
project paco 'https://github.com/snu-sf/paco' 'd0561bf7f0a96cac486ba3bd8ca0b72ce01fb9cf'
# Contact @minkiminki on github

########################################################################
# coq-itree
########################################################################
project itree 'https://github.com/DeepSpec/InteractionTrees' 'cf1443c88aca8691d93ce84fc633145752e7944e'
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
project json 'https://github.com/liyishuai/coq-json' '8069b6b4d544ea3011246dfa04d2c1c550d50455'
# Contact @liyishuai on github

########################################################################
# coq-async-test
########################################################################
project async_test 'https://github.com/liyishuai/coq-async-test' '0637b95ae52060d8a808261ca97890d03c9a4503'
# Contact @liyishuai on github

########################################################################
# coq-http
########################################################################
project http 'https://github.com/liyishuai/coq-http' 'cabde79a4a0d978d031475c7443be7fd43a711c5'
# Contact @liyishuai on github

########################################################################
# paramcoq
########################################################################
project paramcoq 'https://github.com/coq-community/paramcoq' '937537d416bc5f7b81937d4223d7783d0e687239'
# Contact @ppedrot on github

########################################################################
# relation_algebra
########################################################################
project relation_algebra 'https://github.com/damien-pous/relation-algebra' '4db15229396abfd8913685be5ffda4f0fdb593d9'
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

project verdi 'https://github.com/uwplse/verdi' 'b7f77848819878b1faf0e2e6a730f9bb850130be'
# Contact @palmskog on github

project verdi_raft 'https://github.com/uwplse/verdi-raft' 'a3375e867326a82225e724cc1a7b4758b029376f'
# Contact @palmskog on github

########################################################################
# Stdlib
########################################################################
project stdlib 'https://github.com/coq/stdlib' '2b23d2d3b313d5fe8b54a649a4aca6977a144648'
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
project perennial 'https://github.com/mit-pdos/perennial' 'b39e2c342ba3da95e11a7db31c7be20560e92cae'
# Contact @upamanyus, @RalfJung, @tchajed on github
# PRs to fix Perennial failures should be submitted against the Perennial
# `master` branch. `coq/tested` is automatically updated every night to the
# `master` branch if CI on `master` is green. This is to avoid breaking Coq CI
# when Perennial CI breaks.

########################################################################
# metarocq
########################################################################
project metarocq 'https://github.com/MetaRocq/metarocq' '57619a62980c4d92ec2122ddb312c3d4adfd8431'
# Contact @mattam82, @yforster on github

########################################################################
# SF suite
########################################################################
project sf 'https://github.com/DeepSpec/sf' '5e863a9f92e515a0e11641f28077a64919f8482e'
# Contact @bcpierce00, @liyishuai on github

########################################################################
# Coqtail
########################################################################
project coqtail 'https://github.com/whonore/Coqtail' '28340858a528a6e86d3eee2ff5ccbf56f3eaf43f'
# Contact @whonore on github

########################################################################
# Deriving
########################################################################
project deriving 'https://github.com/arthuraa/deriving' '04105e8303199e588e0074e28123fd86c8c420f7'
# Contact @arthuraa on github

########################################################################
# VsRocq
########################################################################
project vsrocq 'https://github.com/rocq-prover/vsrocq' '93560217d1fa5c2b473718703007bd292719c2fc'
# Contact @rtetley, @gares on github

########################################################################
# category-theory
########################################################################
project category_theory 'https://github.com/jwiegley/category-theory' '42684ff22decc06afeb4caeb31249b1e498cb1ce'
# Contact @jwiegley on github

########################################################################
# itauto
########################################################################
project itauto 'https://gitlab.inria.fr/fbesson/itauto' 'ff11a568d000b94965a33de428c6e6700b920198'
# Contact @fajb on github

########################################################################
# Mathcomp-word
########################################################################
project mathcomp_word 'https://github.com/jasmin-lang/coqword' 'a34107995570598dd3844b530924db83e1c82932'
# Contact @vbgl, @strub on github

########################################################################
# Jasmin
########################################################################
project jasmin 'https://github.com/jasmin-lang/jasmin' 'c8188deeedf67e7633b4fbda4aacb13da14cba61'
# Contact @vbgl, @bgregoir on github

########################################################################
# Lean Importer
########################################################################
project lean_importer 'https://github.com/coq-community/rocq-lean-import' 'c3546102f242aaa1e9af921c78bdb1132522e444'
# Contact @SkySkimmer on github

########################################################################
# SMTCoq
########################################################################
project smtcoq 'https://github.com/smtcoq/smtcoq' '5c6033c906249fcf98a48b4112f6996053124514'
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
project tactician 'https://github.com/coq-tactician/coq-tactician' '3a74c377ac9409d425f11f679eff7a34eaa5a45a'
# Contact @LasseBlaauwbroek on github

########################################################################
# Ltac2 compiler
########################################################################
project ltac2_compiler 'https://github.com/SkySkimmer/coq-ltac2-compiler' '2ee3660aad17b0310c07bab6ce94efdd45b67212'
# Contact @SkySkimmer on github

########################################################################
# Waterproof
########################################################################
project waterproof 'https://github.com/impermeable/coq-waterproof' 'dd712eb0b7f5c205870dbd156736a684d40eeb9a'
# Contact @jellooo038, @jim-portegies on github

########################################################################
# Autosubst (2) OCaml
########################################################################
project autosubst_ocaml 'https://github.com/uds-psl/autosubst-ocaml' 'a4e154fb548197572326167809a4c612a2ec71ac'
# Contact @yforster on github

########################################################################
# Trakt
########################################################################
project trakt 'https://github.com/ecranceMERCE/trakt' '956e78ab3680d186d03d8b58dbd90681174f3157'
# Contact @ckeller, @louiseddp on github
