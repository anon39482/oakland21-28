In order to reproduce results from the IEEE S&P submission, follow these steps:

# Install and run nix-shell

  ```
  curl -L https://nixos.org/nix/install | sh
  . ~/.nix-profile/etc/profile.d/nix.sh
  nix-shell
  ```

# Build jasmin compiler using nix

Inside nix-shell run

  ```
  cd compiler
  make CIL build
  exit
  ```

This will build compiler/jasminc; you may want to add the directory to your PATH variable:

  ```
  export PATH=$PATH:`pwd`/compiler
  ```


# Check speculative constant-time and safety

The Poly1305 and ChaCha20 examples are in the subdirectory compiler/sct-examples.
For details on how to run the checks, please the file compiler/README-SCT.md


# Functional correcness

The functional correctness proofs will be provided on request, and can be checked using EasyCrypt