FROM ubuntu:latest
WORKDIR /work
COPY . .
RUN apt update && apt install build-essential cmake xorg-dev  -y
WORKDIR /work/build
RUN cmake .. -DCMAKE_BUILD_TYPE=Debug
CMD [ "make" ]