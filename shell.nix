with (import <nixpkgs> {}).pkgs;
let pkg = haskellngPackages.callPackage
            ({ mkDerivation, alex, array, base, BNFC, directory, filepath
             , happy, haskeline, mtl, stdenv, transformers
             }:
             mkDerivation {
               pname = "cubical";
               version = "0.2.0";
               src = ./.;
               isLibrary = false;
               isExecutable = true;
               buildDepends = [
                 array base BNFC directory filepath haskeline mtl transformers
               ];
               buildTools = [ alex happy ];
               homepage = "https://github.com/simhu/cubical";
               description = "Implementation of Univalence in Cubical Sets";
               license = stdenv.lib.licenses.mit;
             }) {};
in
  pkg.env
