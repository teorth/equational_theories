#!/usr/bin/env bash

# set script to fail if we encounter an error
set -e

if ! [[ "$(python3 --version)" =~ Python\ 3\.11.* ]]; then
    echo "Warning! You are not using Python version 3.11"
    echo "These scripts were developed with that version in mind, so use at your own risk!"
fi

if [ ! -f requirements.txt ]; then
    echo "requirments.txt not found! Are you sure you are in the root project directory?"
    return
fi

# create and activate virtual environment
if [ ! -d ".venv" ]; then
    echo "Virtual environment not found. Creating one..."
    python3 -m venv .venv
fi

echo "Activating environment..."
source .venv/bin/activate

# install packages
pip3 install -r requirements.txt
