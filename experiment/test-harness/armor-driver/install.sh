pip3 install pyinstaller

rm -rf ~/.residuals 2> /dev/null
rm -rf ~/.armor 2> /dev/null
rm -rf build/ 2> /dev/null
rm -rf bin/ 2> /dev/null
rm armor-driver.spec 2> /dev/null

mkdir ~/.residuals
mkdir ~/.armor

cp armor-bin ~/.armor/armor-bin
cp morpheus-bin ~/.armor/morpheus-bin
cp hash-hacl-star-bin ~/.armor/hash-hacl-star-bin

python3 -m PyInstaller driver.py --onefile --name=armor-driver --distpath bin

echo "Installation Complete!"  
