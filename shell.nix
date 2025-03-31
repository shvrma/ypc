{
  pkgs ?
    import
      (builtins.fetchTarball "https://api.github.com/repos/NixOs/nixpkgs/tarball/44f5040eb89b9c50717c4c974206c5c93b647ca6")
      {
        overlays = [
          (import (
            builtins.fetchTarball "https://api.github.com/repos/oxalica/rust-overlay/tarball/011de3c895927300651d9c2cb8e062adf17aa665"
          ))
        ];
      },
}:

pkgs.mkShell {
  packages = [ pkgs.rust-bin.stable.latest.default ];
}
