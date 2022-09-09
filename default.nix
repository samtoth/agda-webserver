{ nixpkgs ?  <nixpkgs> }:
with (import nixpkgs {});
let
  agda-effects = import ./../effects/default.nix {};
in
agdaPackages.mkDerivation {
  version = "1.0";
  pname = "agda-webserver";
  src = ./src/..;
  
  buildInputs = [
    agdaPackages.agda-prelude
    agda-effects
  ];

  preBuild = ''
        echo "module Everything where" > Everything.agda
        find src/ -name '*.agda' | sed -e 's/src\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
        
  '';
  
  meta = {};
}
