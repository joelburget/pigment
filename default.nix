# This file was auto-generated by cabal2nix. Please do NOT edit manually!

{ cabal, ghcjsBase, ghcjsDom, ghcjsPrim, lensFamily, mtl, newtype
, reactHaskellGhcjs, void
}:

cabal.mkDerivation (self: {
  pname = "pigment";
  version = "0.2";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  buildDepends = [
    ghcjsBase ghcjsDom ghcjsPrim lensFamily mtl newtype
    reactHaskellGhcjs void
  ];
  meta = {
    homepage = "https://github.com/joelburget/pigment";
    description = "Interactively program dependent types online";
    license = self.stdenv.lib.licenses.mit;
    platforms = self.ghc.meta.platforms;
  };
})
