# Lean class

This is the repository for Robert Samal's class "LEAN – Computer-Assisted Proofs".

It started as a fork of the [repository for Bhavik Mehta's 2025 course on formalising mathematics](https://github.com/b-mehta/formalising-mathematics-notes).

I expect modifications in the latter parts of the semester.


## Local installation

First you need to install Visual Studio Code and the Lean 4 extension. Instructions for doing that are [here](https://leanprover-community.github.io/get_started.html#regular-install).

Then it's just a matter of installing this repository onto your computer. There are two ways to do this.

### Local installation via point-and-click in VS Code

The most painless way to install the repository is using VS Code directly. Install the "Lean 4" extension, and then click on the upside-down A
![an upside-down A](png/clone_forall.png?raw=true "an upside-down A")
and select `Open Project` -> `Project: Download Project`. Type in the following URL into the text box which appeared:

```
https://github.com/robert-samal/lean-class
```

and then select the directory where you want the project installed, type in the name of a folder (for example lean-class) and then wait for a minute or two while everything downloads and compiles. Then accept the suggestion to open the course directory, and you should be up and running. Open up VS Code's file explorer (it looks like this)

![File explorer](png/file_explorer.png?raw=true "File explorer")

and navigate to the `Class_materials` directory, where you should find a whole bunch of directories containing the exercises.

## Online play

If you don't have the 4.5 gigabytes necessary to install all this, or if your computer is too slow to make the experience of using Lean on it fun (you'll need at least 8 gigs of ram, for example), then you can do the course exercises through a web browser (and you don't need to install anything onto your computer using this method).

Just click here: [![Open in Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/robert-samal/lean-class). 
A codespace (linux virtual machine) will be created for you, and github kindly provides some time free of charge. (You may need to
apply for a student/educational account for this to be true.)

## Course notes

https://iuuk.mff.cuni.cz/~samal/vyuka/Lean/
