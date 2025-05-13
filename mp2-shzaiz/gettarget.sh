#!/bin/bash

USER=$(id -un)
curl -s "http://fourier.cs.iit.edu:35103/?username=$USER&usermail=$USER@hawk.iit.edu&submit=Submit" | tar xvf - 
