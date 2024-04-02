## Assumptions

- Stable Internet connection

- `ARMOR/src/armor-agda` is already built and the executable is already placed inside `ARMOR/src/armor-driver`.
   Otherwise, build and install **ARMOR** first, executing `./install.sh` from the `ARMOR` root directory.

## How to Run

- build all libraries in docker environment

  `./run_exp.sh`

- run the experiment inside docker container

  `./diff-test.sh /home/test-harness/sample_root_ca_store.pem /home/Data/ /home/docker_results/`
