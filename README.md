# LA Tech Math 490/587<br/> Integrated Theorem Proving with Lean<br/> Spring 2025
This repository contains the files for [ITPL](https://latechlean.github.io).

## Pre-Requisites
Before getting started, you will need the following:
1. `git`<br/> 
    - Linux/Unix: Most package managers include git.  See [here](https://git-scm.com/downloads/linux) for more details.
    - Mac: Homebrew and MacPorts both include git.  See [here](https://git-scm.com/downloads/mac) for more details.
    - Windows: You can find an installer [here](https://git-scm.com/downloads/win).  You might find 
2. [`VSCode`](https://code.visualstudio.com)
3. [`lean`](https://docs.lean-lang.org/lean4/doc/quickstart.html)

## Setup

1. Clone the repository.
- You can do this within Visual Studio Code using the Source Control menu on the left-hand side.
   - With the Source Control open, click `Clone Repository`.
   - At the top of the VS Code window, click `Clone from GitHub`.
   - In the same menu bar, type in <br/>
   ```
    LATechLean/ITPLxS25
   ```
   - Select a location to put the folder.
   - Click `Open` from the popup window.
   - You can choose to trust the author or not.
- From the command line
    - Change into the directory where you would like clone the repository.
    - Enter the command <br/>
      ```
      git clone https://github.com/LATechLean/ITPLxS25.git
      ```
3. Update
   - From Visual Studio Code, Right click on `ITPLxS25` and select `Open in Integrated Terminal`.
   - Change to the top level of the repository using
     ```
     cd ..
     ```
   - type in
     ```
     lake exe cache get
     ```
 You should have a working repository!
