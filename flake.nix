{
  description = "toatie --- a toy language for hardware description with dependent types";

  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.nixpkgs.url     = github:NixOS/nixpkgs;
  inputs.idris.url       = github:idris-lang/Idris2/v0.5.1;
  inputs.netlistsvg.url  = github:cramsay/netlistsvg;

  outputs = { self, flake-utils, nixpkgs, idris, netlistsvg }:
    flake-utils.lib.eachSystem ["x86_64-linux" "x86_64-darwin"] (system:

      let
        pkgs       = import nixpkgs { inherit system; };
        idrisPkgs  = idris.packages.${system};

        toatiePkg = pkgs.stdenv.mkDerivation ({
          name = "toatie";
          src = ./.;
          doCheck = true;
          nativeBuildInputs = [ # Build phase packages
                                idrisPkgs.idris2
                                # Test suite packages
                                pkgs.ghdl
                                pkgs.yosys
                                pkgs.yosys-ghdl
                                netlistsvg.defaultPackage.${system}
                                pkgs.nodejs-12_x
                              ];
          buildPhase = ''
            make bin
          '';
          checkPhase = ''
            export PATH=$PWD/build/exec:$PATH
            export TOATIE_PATH=$PWD/libs
            make check
          '';
          installPhase = ''
            make install
          '';
        });

      in {

        packages = { toatie = toatiePkg; };
        defaultPackage = toatiePkg;

        devShell = pkgs.mkShell {
          shellHook = ''
            export PATH=$PWD/build/exec:$PATH
            export TOATIE_PATH=$PWD/libs
            alias devEmacs="${idris.packages.${system}.idris-emacs}/bin/emacs --eval \"(require 'idris2-mode)\" &"
            alias devTest="(cd $PWD; make check)"
            alias devBuild="(cd $PWD; make bin)"
            alias devRepl="$PWD/build/exec/toatie"
          '';

          buildInputs = [
            (idris.packages.${system}.idris2)
            (idris.packages.${system}.emacs-with-idris)
            pkgs.gtkwave
            pkgs.ghdl
            pkgs.yosys
            pkgs.yosys-ghdl
            netlistsvg.defaultPackage.${system}
            pkgs.nodejs-12_x
          ];
        };

      }
    );
}
