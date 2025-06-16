FROM janschultecom/docker-liquidhaskell

RUN apt-get update
RUN apt-get install -y vim emacs make

COPY .vimrc /root/.vimrc
COPY .emacs /root/.emacs

WORKDIR /data
