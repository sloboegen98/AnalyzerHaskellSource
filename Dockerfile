FROM openjdk:8

RUN apt-get -y update && apt-get -y upgrade
RUN apt-get install -y g++ make uuid-dev cmake git pkg-config

# Download ANTLR
ENV ANTLR_VERSION 4.8
RUN cd /usr/local/lib && curl -O https://www.antlr.org/download/antlr-${ANTLR_VERSION}-complete.jar
ENV CLASSPATH .:/usr/local/lib/antlr-${ANTLR_VERSION}-complete.jar:$CLASSPATH
RUN alias antlr4='java -Xmx500M -cp "/usr/local/lib/antlr-${ANTLR_VERSION}-complete.jar:$CLASSPATH" org.antlr.v4.Tool'

# Download CPP-runtime
RUN git clone https://github.com/antlr/antlr4/
RUN cd antlr4/runtime/Cpp && \
    mkdir build && mkdir run && cd build && \
    cmake .. -DANTLR_JAR_LOCATION=/usr/local/lib/antlr-${ANTLR_VERSION}-complete.jar -DWITH_DEMO=True && \
    make && make install

RUN mkdir Haskell_CPP
COPY ./Haskell_CPP /Haskell_CPP

RUN cd /Haskell_CPP/ && make
RUN ldconfig -v

WORKDIR /Haskell_CPP/

CMD ["make", "test"]

