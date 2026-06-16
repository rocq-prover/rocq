{

  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";

  outputs =
    {
      self,
      nixpkgs,
    }:
    let
      inherit (nixpkgs) lib;
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      eachSystem = lib.genAttrs systems;
      pkgsFor = nixpkgs.legacyPackages;
    in
    {
      packages = eachSystem (
        system:
        let
          pkgs = pkgsFor.${system};
        in
        {
          rocq = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "rocq";

            version = "9.1.0";

            buildInputs = with pkgs; [
              hostname
              python311
              ocamlPackages.yojson
              ocamlPackages.camlzip
              # coq-makefile timing tools
              time
            ];

            nativeBuildInputs = [
              pkgs.pkg-config
            ]
            ++ (with pkgs.ocamlPackages; [
              ocaml
              findlib
              dune_3
            ]);

            propagatedBuildInputs = with pkgs.ocamlPackages; [
              zarith
            ];

            src =
              let
                fs = lib.fileset;
              in
              fs.toSource {
                root = ./.;
                # fileset = fs.difference (fs.gitTracked ./.) (
                #   fs.unions [
                #     # ./doc
                #     ./flake.lock
                #     (fs.fileFilter (file: lib.strings.hasInfix ".git" file.name) ./.)
                #     (fs.fileFilter (file: file.hasExt "svg") ./.)
                #     # (fs.fileFilter (file: file.hasExt "md") ./.)
                #     (fs.fileFilter (file: file.hasExt "nix") ./.)
                #   ]
                # );
                fileset = fs.gitTracked ./.;
              };

            preConfigure = ''
              patchShebangs dev/tools doc/corelib
            '';

            prefixKey = "-prefix ";

            enableParallelBuilding = true;

            buildFlags = [
              # "world"
              "revision"
              "coq"
              "coqide"
            ];

            # TODO, building of documentation package when not in dev mode
            # https://github.com/rocq-prover/rocq/issues/16198
            # buildFlags = [ "world" ] ++ optional buildDoc "refman-html";

            # From https://github.com/NixOS/nixpkgs/blob/master/pkgs/build-support/ocaml/dune.nix

            postPatch = ''
              UNAME=$(type -tp uname)
              RM=$(type -tp rm)
              substituteInPlace tools/beautify-archive --replace-warn "/bin/rm" "$RM"
            '';

            buildPhase = ''
              runHook preBuild

              make dunestrap
              dune build -p rocq-runtime,rocq-core,coq-core,coqide-server -j $NIX_BUILD_CORES

              runHook postBuild
            '';

            # installTargets =
            #   [ "install" ];
            # fixme, do we have to do a target, or can we just do a copy?
            # ++ optional buildDoc "install-doc-html";

            createFindlibDestdir = true;

            doInstallCheck = true;

            preInstallCheck = ''
              patchShebangs tools/
              patchShebangs test-suite/
              export OCAMLPATH=$OCAMLFIND_DESTDIR:$OCAMLPATH
            '';

            installCheckTarget = [ "check" ];

            installPhase = ''
              runHook preInstall

              dune install \
              --prefix $out \
              --libdir $OCAMLFIND_DESTDIR rocq-runtime coq-core rocq-core coqide-server \
              --docdir $out/share/doc \
              --mandir $out/share/man

              ${pkgs.tree}/bin/tree -d $out
              ${pkgs.tree}/bin/tree -d $OCAMLFIND_DESTDIR

              # coq and rocq are now in different directories, which sometimes confuses coq_makefile
              # which expects both in the same /nix/store/.../bin/ directory
              # adding symlinks to content it
              # ROCQBIN=$(dirname '$(command -v rocq)')
              # for b in csdpcert ocamllibdep rocq rocq.byte rocqchk votour ; do
              #   ln -P ''${ROCQBIN}/''${b} $out/bin/
              # done

              runHook postInstall
            '';

            postInstall = ''
              # FIXME: symlinking does not work here.
              # ln -s $out/lib/rocq-runtime $OCAMLFIND_DESTDIR/rocq-runtime
              # ln -s $out/lib/coq-core $OCAMLFIND_DESTDIR/coq-core
              # ln -s $out/lib/coqide-server $OCAMLFIND_DESTDIR/coqide-server

              # mkdir -p "$out/share/pixmaps"
              # ln -s $out/share/coq/coq.png $out/share/pixmaps
            '';

            passthru = {
              rocq-version = finalAttrs.version;
              inherit (finalAttrs) ocamlPackages;
              dontFilter = true; # Useful to use mkCoqPackages from <nixpkgs>
            };

            setupHook = pkgs.writeText "setupHook.sh" ''
              addCoqPath () {
                if test -d "$1/lib/coq/${finalAttrs.version}/user-contrib"; then
                  export ROCQPATH="''${ROCQPATH-}''${ROCQPATH:+:}$1/lib/coq/${finalAttrs.version}/user-contrib/"
                fi
              }

              addEnvHooks "$targetOffset" addCoqPath
            '';

            meta = {
              description = "Rocq Prover";
              longDescription = ''
                The Rocq Prover is an interactive theorem prover, or proof assistant.  It provides a formal language
                to write mathematical definitions, executable algorithms and theorems
                together with an environment for semi-interactive development of
                machine-checked proofs.
              '';
              homepage = "https://rocq-prover.org";
              license = lib.licenses.lgpl21;
              platforms = lib.platforms.unix;
            };
          });
        }
      );
      devShells = eachSystem (system: {

      });
      formatter = eachSystem (system: pkgsFor.${system}.nixfmt);
    };
  # flake-utils.lib.eachDefaultSystem
  # (system: {
  #   packages = with import nixpkgs { inherit system; }; coq.override { version = ./.; };
  #   defaultPackage = self.packages.${system};
  # });
}
