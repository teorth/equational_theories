# PowerShell script

# This powershell script was actually written by ChatGPT asked to convert the shell script version
# seems like it did a fairly good job

# Check if Python version is 3.11
$pythonVersion = & python --version
if ($pythonVersion -notmatch "Python 3\.11.*") {
    Write-Host "Warning! You are not using Python version 3.11"
    Write-Host "These scripts were developed with that version in mind, so use at your own risk!"
}

# Check if requirements.txt exists
if (-not (Test-Path -Path "requirements.txt")) {
    Write-Host "requirements.txt not found! Are you sure you are in the root project directory?"
    return
}

# Check if virtual environment exists
if (-not (Test-Path -Path ".venv")) {
    Write-Host "Virtual environment not found. Creating one..."
    python -m venv .venv
}

# Activate the virtual environment
Write-Host "Activating environment..."
& .\.venv\Scripts\Activate

# Install required packages
pip install -r requirements.txt
