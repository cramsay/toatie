{
  description = "toatie --- a toy language for hardware description with dependent types";

  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.nixpkgs.url     = github:NixOS/nixpkgs;
  inputs.idris.url       = github:idris-lang/Idris2/v0.5.1;

  outputs = { self, flake-utils, nixpkgs, idris }:
    flake-utils.lib.eachSystem ["x86_64-linux" "x86_64-darwin"] (system:

      let

        pkgs       = import nixpkgs { inherit system; };
        idrisPkgs  = idris.packages.${system};
        toatiePkg = pkgs.stdenv.mkDerivation ({
          name = "toatie";
          src = ./.;
          doCheck = true;
          nativeBuildInputs = [ idrisPkgs.idris2 ];
          buildPhase = ''
            make bin
          '';
	  checkPhase = ''
	    export PATH=$PWD/build/exec:$PATH
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
            alias devEmacs="${idris.packages.${system}.idris-emacs}/bin/emacs --eval \"(require 'idris2-mode)\" &"
            alias devTest="(cd $PWD; make check)"
            alias devBuild="(cd $PWD; make bin)"
            alias devRepl="$PWD/build/exec/toatie"
          '';

          buildInputs = [
            (idris.packages.${system}.idris2)
            (idris.packages.${system}.emacs-with-idris)
          ];
        };

      }
    );
}
