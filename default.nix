args@{ agdaPackages ? "agdaPackages"

, rev ? "abc7633e982da7a58cc21b039f54d068f5b00aff"
, sha256 ? "0k3imyx65a7zchigkvzg4z8m01n6jprijba21093sfhzsr3rrc70"

, pkgs ? import (builtins.fetchTarball {
  url = "https://github.com/jwiegley/nixpkgs/archive/${rev}.tar.gz";
  inherit sha256;
}) {
  config.allowUnfree = true;
  config.allowBroken = false;
  overlays = [ ];
} }:

with pkgs.${agdaPackages};

pkgs.stdenv.mkDerivation rec {
  name = "denotational-design-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = [ (agda.withPackages (p: [ p.standard-library ])) ];

  libraryFile = "${libraryName}.agda-lib";
  libraryName = "discovery";

  phases = [ "unpackPhase" "patchPhase" "buildPhase" "installPhase" ];

  buildPhase = ''
    agda -i "." Everything.agda
  '';

  installPhase = ''
    mkdir -p $out
    cp -pR * $out
  '';

  env = pkgs.buildEnv {
    name = name;
    paths = buildInputs;
    buildInputs = with pkgs; [ pandoc pdf2svg ];
  };
}
