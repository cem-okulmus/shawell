# syntax=docker/dockerfile:1

ARG GO_VERSION=1.22

FROM --platform=linux/amd64 golang:${GO_VERSION}-bookworm AS build

WORKDIR /src

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl git bash \
    && rm -rf /var/lib/apt/lists/*

COPY go.mod go.sum ./
RUN go mod download

COPY . .

RUN bash ./download_deps.sh \
    && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -trimpath -ldflags="-s -w" -o /out/shawell . \
    && mkdir -p /out/bin \
    && cp bin/dlv bin/oxigraph /out/bin/

FROM build AS test

ENV PATH="/src/bin:${PATH}"
RUN go test -count=1 ./...

FROM --platform=linux/amd64 debian:bookworm-slim AS runtime

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates bash \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY --from=build /out/shawell /usr/local/bin/shawell
COPY --from=build /out/bin /app/bin
COPY README.md LICENSE ./
COPY resources ./resources

ENV PATH="/app/bin:${PATH}"

ENTRYPOINT ["shawell"]
CMD ["--help"]
