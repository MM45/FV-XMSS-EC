# syntax=docker/dockerfile:1

# Base image: EasyCrypt's release r2026.02
ARG EC_IMAGE=ghcr.io/easycrypt/ec-test-box:r2026.02
FROM ${EC_IMAGE}

# Inherited from base image:
# user/USER: charlie (uid: 1001)
# primary group: root (gid: 0)
# supplementary groups: sudo
# workdir/WORKDIR: /home/charlie

# Create and set working directory in image,
# and copy over repository with appropriate permissions
WORKDIR /work
COPY --chown=charlie:root . /work

# Entrypoint (prepended to initial command, defaulting to CMD)
ENTRYPOINT ["opam", "exec", "--"]

# Default command to run (appended to entrypoint, defaulting to ENTRYPOINT)
CMD ["make", "check"]
