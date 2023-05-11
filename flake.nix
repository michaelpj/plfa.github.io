{
  description = "PLFA";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, flake-utils, nixpkgs }: flake-utils.lib.eachDefaultSystem (system: 
    let pkgs = import nixpkgs { inherit system; };
        agda = pkgs.agda.withPackages (p: [p.standard-library]);
    in {
      devShells.default = pkgs.mkShell { 
        buildInputs = [ agda ]; 
      };
    });
}
