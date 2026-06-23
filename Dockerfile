# Pinned environment for artifact evaluation.
# Build:  docker build -t typaol-artifact .
# Test:   docker run --rm typaol-artifact
FROM haskell:9.12.2

WORKDIR /artifact

# Resolve and cache dependencies first (faster rebuilds on source changes).
COPY timed-typaol.cabal cabal.project ./
RUN cabal update && cabal build --only-dependencies --enable-tests all

COPY . .
RUN cabal build all

CMD ["cabal", "test", "--test-show-details=direct"]
