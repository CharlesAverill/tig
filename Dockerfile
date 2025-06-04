# Modified from https://github.com/blacktop/docker-ghidra, https://gitlab.com/CinCan/tools/
FROM openjdk:21-jdk-slim AS build

ARG tool_version=ghidra_11.3.1_PUBLIC_20250219
ARG tool_tag=Ghidra_11.3.1_build

ENV TOOL_VERSION=$tool_version
ENV TOOL_TAG=$tool_tag
ENV GHIDRA_SHA256=bcda0a9de8993444766cc255964c65c042b291ddaf6c50d654e316e442b441fa

RUN apt-get update && apt-get install -y wget ca-certificates unzip --no-install-recommends \
    && wget --progress=bar:force -O /tmp/ghidra.zip https://github.com/NationalSecurityAgency/ghidra/releases/download/${TOOL_TAG}/${TOOL_VERSION}.zip \
    && echo "$GHIDRA_SHA256 /tmp/ghidra.zip" | sha256sum -c - \
    && unzip /tmp/ghidra.zip \
    && mv $(echo ${TOOL_VERSION} | cut -f1-3 -d"_") /ghidra \
    && chmod +x /ghidra/ghidraRun  \
    #&& apt-get clean 
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/* /var/cache/apt/archives /tmp/* /var/tmp/* /ghidra/docs /ghidra/Extensions/Eclipse /ghidra/licenses

ARG guest_uid=1000
ARG guest_gid=${guest_uid}
ARG guest_name=appuser

WORKDIR /ghidra

RUN mkdir /ghidra/projects/

RUN du -sh /ghidra

COPY ghidra_scripts/ /ghidra_scripts/


# Disable illegal reflective access warnings to just produce decompiled code

RUN apt-get update && apt-get install -y sudo libxml2-utils vim \
    && echo "===> Clean up unnecessary files..." \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/* /var/cache/apt/archives /tmp/* /var/tmp/*

RUN sed -i '/VMARG_LIST+="-XX:CICompilerCount=2 "/a VMARG_LIST+="--add-opens java.base/java.lang=ALL-UNNAMED"' /ghidra/support/analyzeHeadless


RUN groupadd -g ${guest_gid} ${guest_name} \
    && useradd --no-log-init -m -s /bin/bash -g ${guest_name} -G sudo -p '' -u ${guest_uid} ${guest_name}


RUN mv /ghidra_scripts/_run.sh /ghidra
RUN chmod +x /ghidra/_run.sh

RUN chown -R ${guest_name}:${guest_name} /ghidra

USER ${guest_name}

# Define ghidra location for script, it is expecting $GHIDRA_HOME variable
ENV GHIDRA_HOME=/ghidra
WORKDIR /ghidra

ENTRYPOINT ["/ghidra/_run.sh" ]
