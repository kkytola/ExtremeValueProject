# Extreme value distribution project

 * [Blueprint](https://kkytola.github.io/ExtremeValueProject/)

This project is a part of the course *MS-EV0029 Introduction to Formalized Mathematics in Lean* at Aalto University, February-June 2025. Course participants are welcome to contribute following the guidelines below:
 1. Claim an issue (or suggest an issue if no issue exists for something essential for the project).
 2. Wait until the issue is assigned to you, in order to avoid duplicated effort.
 3. Work on the issue on your own fork of the repository (and remember to sync your fork regularly to get up-to-date work by other contributors).
 4. Once you are ready, create a pull-request (PR) from your fork (via *Contribute*) to this repository. The PR message should mention `close #N` where N is the number of the issue. (You may also make PRs which make partial progress or are not directly related to issues.)
 5. The PR is reviewed and modifications may be suggested. Discuss the proposed modifications and adjust accordingly.
 6. The PR is either merged or closed. In the first case, the issue is closed. In the second case, indicate whether you plan to still work on the issue, so that issue assignment can be updated if needed.

## Blueprint

The blueprint is written with [Verso Blueprint](https://github.com/leanprover/verso-blueprint).
Its sources are Lean files in the separate Lake package in the `blueprint` folder
(one module per chapter in `blueprint/ExtremeValueProjectBlueprint/Chapters`).
To build it locally:
```
cd blueprint
lake exe cache get
lake exe vbp build          # writes the web version to _out/site/html-multi
lake exe vbp build --serve  # builds and serves the web version locally
```
