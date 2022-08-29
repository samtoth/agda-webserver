{ nixpkgs ?  <nixpkgs> }:
with (import nixpkgs {});
agdaPackages.mkDerivation {
  version = "1.0";
  pname = "agda-webserver";
  src = ./src;
  buildInputs = [
    agdaPackages.agda-prelude
  ];

  preBuild = ''
           
  '';
  
  meta = {};
}
