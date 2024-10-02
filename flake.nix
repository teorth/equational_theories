{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in
    { devShell.${system} = pkgs.stdenv.mkDerivation rec {
      name = "env";
      buildInputs = with pkgs; [
        elan
        python3
        python3Packages.numpy
        python3Packages.z3-solver
        python3Packages.networkx
      ];
   };};
}
