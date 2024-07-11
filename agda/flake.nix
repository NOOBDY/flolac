# https://gist.github.com/aciceri/153ae85c63940847c8d3138895d77dd2
{
  description = "The HoTT Game Enviroment";
  nixConfig.bash-prompt-prefix = "(agda)";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
    emacs-overlay.url = "github:nix-community/emacs-overlay";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      emacs-overlay,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ emacs-overlay.overlays.default ];
        };
        shell = pkgs.mkShell {
          buildInputs = [
            pkgs.emacs
            pkgs.emacsPackages.agda2-mode
            (pkgs.agda.withPackages (ps: [
              ps.standard-library
              ps.cubical
            ]))
          ];
        };
      in
      {
        formatter = nixpkgs.legacyPackages.x86_64-linux.nixfmt-rfc-style;
        devShell = shell;
      }
    );
}
