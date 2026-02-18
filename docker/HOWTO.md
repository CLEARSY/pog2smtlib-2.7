# HOWTO build and push the docker image

## Build and push the image to GitHub registry

CR_PAT is a GitHub token with the "write:packages" scope.

```sh
echo $CR_PAT | docker login ghcr.io -u dde_cls --password-stdin
docker build -t ghcr.io/clearsy/dolmen:latest .
docker push ghcr.io/clearsy/dolmen:latest
```
