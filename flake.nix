{
  description = "A flake for building Hello World";

  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixos-20.03;
  inputs.idris2-dev.url = github:idris-lang/Idris2;

  outputs = { self, flake-utils, nixpkgs, idris2-dev }:
    flake-utils.lib.eachSystem ["x86_64-linux" "x86_64-darwin"] (system:
      let pkgs = import nixpkgs { inherit system; };
      in {
        devShell = pkgs.mkShell {

		  shellHook = ''
			${idris2-dev.packages.${system}.idris-emacs}/bin/emacs --eval "(require 'idris2-mode)" &
          '';

          buildInputs = [
            (idris2-dev.packages.${system}.idris2)
            (idris2-dev.packages.${system}.emacs-with-idris)
          ];
        };
      }
    );
}
