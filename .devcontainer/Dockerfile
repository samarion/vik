# Debian trixie for TeX Live 2024 (Ubuntu 24.04 has 2023).
FROM mcr.microsoft.com/devcontainers/base:trixie

# LaTeX toolchain for the LaTeX Workshop extension (latexmk + pdflatex +
# bibtex/biber). acmart and llncs live in texlive-publishers; the fonts
# these classes load (libertinus, libertine, newtx, inconsolata) in
# texlive-fonts-extra; stmaryrd in texlive-science; binhex.tex (needed by
# acmart) in texlive-plain-generic.
#
# ceurart, the CEUR-WS class of the SMT workshop, is not on CTAN, so no
# TeX Live has it: ceurart.cls goes with the paper's sources, from
# https://ceur-ws.org/Vol-XXX/CEURART.zip. Its sample builds here with
# pdflatex (`latexmk -pdf`, LaTeX Workshop's default recipe), not with
# lualatex: the class's pdfx fails under LuaTeX, with or without
# -shell-escape.
#
# poppler-utils lets Claude read the PDF's pages (pdftoppm). tmux keeps long
# jobs alive across VS Code reconnects (see shutdownAction in
# devcontainer.json).
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        tmux \
        poppler-utils \
        latexmk \
        biber \
        texlive-latex-extra \
        texlive-fonts-extra \
        texlive-publishers \
        texlive-bibtex-extra \
        texlive-plain-generic \
        texlive-science \
    && rm -rf /var/lib/apt/lists/*

# What the build, the tests and the benchmarks run besides the JVM, in a layer
# of its own so that the TeX Live one above stays cached:
# - clang, clang++ and lld (Debian's LLVM) for the Scala Native rows. With a
#   system clang VIK_NATIVE_FLAGS stays unset: only laraserver4's user-space
#   LLVM needs it.
# - zlib1g-dev for GraalVM's native-image (bench/graal.sh), which also needs
#   the gcc of the base image.
# - python3-venv and pip for bench/.venv (see postCreateCommand), bc for
#   bench/cold.sh, cloc to count lines.
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        clang \
        lld \
        llvm \
        zlib1g-dev \
        python3-venv \
        python3-pip \
        bc \
        cloc \
    && rm -rf /var/lib/apt/lists/*

# The JVM side, system-wide and read-only: the caches that sbt and coursier
# fill at run time stay in the user's home. coursier; the latest LTS JDK
# (Temurin 25) and the GraalVM Community of the same release, which
# sbt-native-image uses instead of fetching its own (NATIVE_IMAGE_INSTALLED);
# the sbt runner, which starts the sbt of project/build.properties; Scala 3's
# `scala` and `scala-cli`. Another JDK, such as the CI matrix's 17 and 27, is
# one `cs java --jvm 17` away.
#
# The JDK's commands and native-image are linked into /usr/local/bin rather
# than put on PATH: a login shell, such as a tmux window, starts from Debian's
# /etc/profile, which resets PATH and keeps /usr/local/bin.
ARG SBT_VERSION=2.1.0
RUN curl -fsSL https://github.com/coursier/coursier/releases/latest/download/cs-x86_64-pc-linux.gz \
        | gzip -d > /usr/local/bin/cs \
    && chmod +x /usr/local/bin/cs \
    && export COURSIER_CACHE=/opt/coursier/cache COURSIER_ARCHIVE_CACHE=/opt/coursier/jvm \
    && mkdir -p /opt/java \
    && ln -s "$(cs java-home --jvm temurin:25)" /opt/java/temurin-25 \
    && ln -s "$(cs java-home --jvm graalvm-community:25)" /opt/java/graalvm-25 \
    && ln -s /opt/java/temurin-25/bin/* /opt/java/graalvm-25/bin/native-image /usr/local/bin/ \
    && curl -fsSL https://github.com/sbt/sbt/releases/download/v$SBT_VERSION/sbt-$SBT_VERSION.tgz \
        | tar -xz -C /opt \
    && ln -s /opt/sbt/bin/sbt /usr/local/bin/sbt \
    && cs install --install-dir /usr/local/bin scala scala-cli \
    && rm -rf /opt/coursier/cache \
    && chmod -R a+rX /opt/coursier
ENV JAVA_HOME=/opt/java/temurin-25 \
    GRAALVM_HOME=/opt/java/graalvm-25 \
    NATIVE_IMAGE_INSTALLED=true

# gh's login, Codex's state, the shell history and the scratch folder, in
# volumes that a rebuild keeps (see the mounts of devcontainer.json). The
# directories are made here, in the home folder, so that a new volume takes
# their owner, the user, whose uid VS Code then updates to the host user's
# along with the rest of the home folder.
# Bash writes each command to the history as it runs, not when it exits: the
# shells of a stopped container do not exit.
RUN mkdir -p /home/vscode/.config/gh /home/vscode/.codex /home/vscode/.shell-history /home/vscode/scratch \
    && chown -R vscode:vscode /home/vscode/.config /home/vscode/.codex /home/vscode/.shell-history /home/vscode/scratch \
    && printf '%s\n' \
        '' \
        '# The history in a volume that a rebuild keeps (see .devcontainer/Dockerfile).' \
        'export HISTFILE=/home/vscode/.shell-history/bash_history HISTSIZE=100000 HISTFILESIZE=100000' \
        'PROMPT_COMMAND="history -a${PROMPT_COMMAND:+; $PROMPT_COMMAND}"' \
        >> /home/vscode/.bashrc
