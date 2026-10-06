# Lean -- Computer-assisted proofs

This is the repository for Robert Samal's 2026 course on using Lean theorem prover for mathematical proofs. The course runs from October 2026. 
It started as a fork of the repository for [Bhavik Mehta's course on formalising mathematics](https://github.com/b-mehta/formalising-mathematics-notes), 
some things will be different though. 

This course is written in Lean 4. 

## Local installation

First you need to install Visual Studio Code and the Lean 4 extension. Instructions for doing that are [here](https://leanprover-community.github.io/get_started.html#regular-install).

Then it's just a matter of installing this repository onto your computer. There are two ways to do this.

### Local installation via point-and-click

The most painless way to install the repository is using VS Code directly. With Lean installed, open any file on your system in VS Code, and then click on the upside-down A

![an upside-down A](png/clone_forall.png?raw=true "an upside-down A")

and select `Open Project` -> `Project: Download Project`. Type in the following URL into the text box which appeared:

```
https://github.com/robert-samal/lean-class
```

and then select the directory where you want the project installed, type in the name of a folder (for example formalising-mathematics-2026) and then wait for a minute or two while everything downloads and compiles. Then accept the suggestion to open the course directory, and you should be up and running. Open up VS Code's file explorer (it looks like this)

![File explorer](png/file_explorer.png?raw=true "File explorer")

and navigate to the `LeanComputerAssistedProofs2026` directory, where you should find a whole bunch of directories containing the exercises.

**Important**: if you see messages saying that it's building mathlib, with something like `[4/209] Building ...`, this isn't good! Instead, click the upside-down A again, then Project Actions, then Fetch Mathlib Build Cache.

### Local installation via command line

An older way is via the command line. Fire up the same command line which you used to install Lean 4 and type this:

```bash
git clone https://github.com/robert-samal/lean-class
cd lean-class
lake exe cache get
```

Now open the folder which you just created, using VS Code's "open folder" functionality. You will find all the exercises for the course inside a subdirectory called `LeanComputerAssistedProofs2026` (this is a subdirectory of the cloned repository).

## Online play

If you don't have the 4.5 gigabytes necessary to install all this, or if your computer is too slow to make the experience of using Lean on it fun (you'll need at least 8 gigs of ram, for example), then you can do the course exercises through a web browser (and you don't need to install anything onto your computer using this method).

### Method 1: via Gitpod.

Just click here: [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/robert-samal/lean-class)

### Method 2: via Codespaces

Just click here: [![Open in Codespaces](https://github.com/codespaces/badge.svg)](https://github.com/robert-samal/lean-class)

