echo Generating web pages and PDFs

echo ULC...
make DIR=. ROOT=ULC/All.lagda

echo PCF...
make DIR=. ROOT=PCF/All.lagda

echo Scheme...
make DIR=. ROOT=Scheme/All.lagda

echo ...finished