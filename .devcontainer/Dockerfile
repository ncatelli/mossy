# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.217.4/containers/rust/.devcontainer/base.Dockerfile

# [Choice] Debian OS version (use bullseye on local arm64/Apple Silicon): buster, bullseye
ARG VARIANT="buster"
FROM mcr.microsoft.com/vscode/devcontainers/rust:0-${VARIANT}

# [Optional] Uncomment this section to install additional packages.
RUN echo 'deb http://deb.debian.org/debian bullseye-backports main contrib non-free' >> /etc/apt/sources.list \
	&& echo 'deb-src http://deb.debian.org/debian bullseye-backports main contrib non-free' >> /etc/apt/sources.list \
	&& apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends \
	linux-perf-5.15
