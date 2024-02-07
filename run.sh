# lake build
rm -rf _out/walkthroughsite
lake exe walkthrough --output _out/walkthroughsite
python3 -m http.server 8800 --directory _out/walkthroughsite