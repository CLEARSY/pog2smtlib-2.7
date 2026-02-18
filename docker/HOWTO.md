# HOWTO build and push the docker image

```sh
docker login registry.gitlab.clearsy.com:443
docker build -t registry.gitlab.clearsy.com:443/atelierb/pog2smtlib-2.7/dolmen .
docker push registry.gitlab.clearsy.com:443/atelierb/pog2smtlib-2.7/dolmen
```
