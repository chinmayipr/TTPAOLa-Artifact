# Pinned environment for artifact evaluation.
# Build:  docker build -t ttpaola-artifact .
# Test:   docker run --rm ttpaola-artifact
FROM haskell:9.12.2

WORKDIR /artifact

# Resolve and cache dependencies first (faster rebuilds on source changes).
COPY timed-ttpaola.cabal cabal.project ./
RUN cabal update && cabal build --only-dependencies --enable-tests all

COPY . .
RUN cabal build all

CMD ["cabal", "test", "--test-show-details=direct"]
