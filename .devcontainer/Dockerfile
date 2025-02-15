FROM mcr.microsoft.com/vscode/devcontainers/base
USER vscode
ENV HOME=/home/vscode

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="$HOME/.elan/bin:$PATH"