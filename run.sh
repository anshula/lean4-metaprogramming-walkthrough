# lake clean
# lake build
rm -rf _out/walkthroughsite # clear old output
lake exe walkthrough --output _out/walkthroughsite # add new output
cp -r website/static_files _out/walkthroughsite/static # add in css
python3 -m http.server 8800 --directory _out/walkthroughsite # start webserver