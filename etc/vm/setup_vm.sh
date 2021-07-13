#!/usr/bin/env bash

# This script sets up the dependencies for the artifact in the VM.
# Note that the script is hardcoded for the user "boogie" (see "sudo su boogie"
# in script) --> change it to whatever user you want to specify.
#
# run "sudo setup_vm.sh" in the home directory of the user that you specify.
# Make sure to source .profile after this has run to get the updated PATH.

export DEBIAN_FRONTEND=noninteractive
# *** General dependencies ***

apt-get update

#Virtual box guest addition dependencies
apt install -y build-essential linux-headers-$(uname -r)
# install additions via VirtualBox GUI

# basic tools
apt-get install git unzip python3

# isabelle dependencies
apt-get -y update && \
apt-get install -y curl less libfontconfig1 libgomp1 libwww-perl pwgen rlwrap unzip && \
apt-get clean

# ***.NET Core SDK 3.1***
wget https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
dpkg -i packages-microsoft-prod.deb

dpkg --purge packages-microsoft-prod && dpkg -i packages-microsoft-prod.deb

apt-get update; \
apt-get install -y apt-transport-https && \
apt-get update && \
apt-get install -y dotnet-sdk-3.1

rm -rf packages-microsoft-prod.deb

# ********Run remaining commands as boogie user********
sudo su boogie <<-'EOF'
    echo "Setting up dependencies folder"

    mkdir deps
    cd deps

    # ***Isabelle***
    echo "Installing Isabelle"

    # download and unpack isabelle
    wget https://isabelle.in.tum.de/dist/Isabelle2021_linux.tar.gz
    tar -xzf Isabelle2021_linux.tar.gz
    rm -rf Isabelle2021_linux.tar.gz

    # add Isabelle to PATH
    echo 'export PATH="$HOME/deps/Isabelle2021/bin:$PATH"' >> ~/.profile

    # ***Z3 4.8.7***
    echo "Installing Z3"
    wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.7/z3-4.8.7-x64-ubuntu-16.04.zip
    unzip z3-4.8.7-x64-ubuntu-16.04.zip
    rm -rf z3-4.8.7-x64-ubuntu-16.04.zip
    mv z3-4.8.7-x64-ubuntu-16.04/ z3-4.8.7
    # add z3 to PATH
    echo 'export PATH="$HOME/deps/z3-4.8.7/bin:$PATH"' >> ~/.profile

    # clone and compile corresponding original boogie versoin
    git clone https://github.com/boogie-org/boogie boogie_orig
    cd boogie_orig
    git checkout 3d09d0b07756
    cd ..
    dotnet build boogie_orig/Source/Boogie.sln
    # add original boogie tool to path (after renaming)
    mv boogie_orig/Source/BoogieDriver/bin/Debug/netcoreapp3.1/BoogieDriver boogie_orig/Source/BoogieDriver/bin/Debug/netcoreapp3.1/boogieorig
    echo 'export PATH="$HOME/deps/boogie_orig/Source/BoogieDriver/bin/Debug/netcoreapp3.1/:$PATH"' >> ~/.profile

    # clone boogie version used for test suite
    git clone https://github.com/boogie-org/boogie boogie_testsuite
    cd boogie_testsuite
    git checkout b4be7f72e3c74cfa9257f385
    rm -rf Test/civl
    cd .. 

    # download boogie vc version from google drive (command taken from https://gist.github.com/iamtekeste/3cdfd0366ebfd2c0d805#gistcomment-2316906)
    wget --load-cookies /tmp/cookies.txt "https://docs.google.com/uc?export=download&confirm=$(wget --quiet --save-cookies /tmp/cookies.txt --keep-session-cookies --no-check-certificate 'https://docs.google.com/uc?export=download&id=1zY0UgHT6fmeripzlzpmd8OM6tUGSJXxv' -O- | sed -rn 's/.*confirm=([0-9A-Za-z_]+).*/\1\n/p')&id=1zY0UgHT6fmeripzlzpmd8OM6tUGSJXxv" -O boogie_vc.zip && rm -rf /tmp/cookies.txt
    unzip boogie_vc.zip
    rm -rf boogie_vc.zip

    dotnet build boogie_vc/Source/Boogie.sln
    # add boogie vc version to path (after renaming)
    mv boogie_vc/Source/BoogieDriver/bin/Debug/netcoreapp3.1/BoogieDriver boogie_vc/Source/BoogieDriver/bin/Debug/netcoreapp3.1/boogievc
    echo 'export PATH="$HOME/deps/boogie_vc/Source/BoogieDriver/bin/Debug/netcoreapp3.1/:$PATH"' >> ~/.profile

    cd ..
    echo "Finished setting up dependencies folder"

    # ********Artifact folder setup********
    echo "Setting up artifact folder"

    mkdir artifact
    cd artifact
    # clone boogie formalization
    git clone https://github.com/gauravpartha/foundational_boogie/
    cd foundational_boogie
    git checkout 26245973788c
    cd ..

    # add boogie session to ROOTS
    echo "~/artifact/foundational_boogie/BoogieLang" >> ~/deps/Isabelle2021/ROOTS

    # create heap image (option -b) for BoogieLang session so that BoogieLang session
    # does not have to be re-checked every time
    ~/deps/Isabelle2021/bin/isabelle build -b -j4 -d ~/artifact/foundational_boogie/BoogieLang Boogie_Lang

    # clone and compile boogie proof generation tool
    git clone https://github.com/gauravpartha/boogie_proofgen/
    cd boogie_proofgen
    git checkout fca0aa6bb01
    cd ..

    dotnet build boogie_proofgen/Source/Boogie.sln
    # add boogie proof generation tool to path (after renaming)
    mv boogie_proofgen/Source/BoogieDriver/bin/Debug/netcoreapp3.1/BoogieDriver boogie_proofgen/Source/BoogieDriver/bin/Debug/netcoreapp3.1/boogieproof
    echo 'export PATH="$HOME/artifact/boogie_proofgen/Source/BoogieDriver/bin/Debug/netcoreapp3.1/:$PATH"' >> ~/.profile

    cd ..
    echo "Finished setting up artifact folder"


    # ********Finalize********

    # add boogiephases to PATH
    mkdir local_scripts
    cp artifact/boogie_proofgen/etc/scripts/boogiephases local_scripts/
    chmod +x ~/local_scripts/boogiephases
    echo 'export PATH="$HOME/local_scripts:$PATH"' >> ~/.profile

    # copy README
    cp artifact/boogie_proofgen/etc/vm/README.md README.md

    echo "Finished setup."
EOF
