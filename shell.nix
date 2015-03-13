{ }:

with import <nixpkgs> {};
let haskellPackages = pkgs.haskellPackages_ghcjs.override {
      extension = self: super: {
        reactHaskellGhcjs = self.callPackage ../react-haskell {};
        pigment = self.callPackage ./. {};
      };
    };

in pkgs.callPackage ./. {
     cabal = haskellPackages.cabal.override {
       extension = self: super: {
         buildTools = super.buildTools ++ [ haskellPackages.ghc.ghc.parent.cabalInstall ];
       };
     };
     inherit (haskellPackages) ghcjsBase ghcjsDom ghcjsPrim lensFamily
                               mtl newtype reactHaskellGhcjs void
                               recursionSchemes;
   }
