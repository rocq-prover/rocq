# This is an example of how to set up a Rocq CI runner on gcloud.
# You will need a single-use API token from https://gitlab.inria.fr/groups/coq/-/runners
# This script is unlikely to be useful unchanged, read and edit to yout environment.

gcloud compute instances create andreser-coq-ci-runnner-2 \
    --project=frog-ext \
    --zone=us-central1-a \
    --tags=restricted-ssh-access \
    --machine-type=c3d-standard-30 \
    --network-interface=network=default,network-tier=PREMIUM,nic-type=GVNIC,stack-type=IPV4_ONLY \
    --metadata=startup-script="
set -x
sudo su -c \"curl -sSL https://get.docker.com/ | sh\";

sudo curl -L --output /usr/local/bin/gitlab-runner https://gitlab-runner-downloads.s3.amazonaws.com/latest/binaries/gitlab-runner-linux-amd64
sudo chmod +x /usr/local/bin/gitlab-runner

/usr/local/bin/gitlab-runner register --non-interactive --url https://gitlab.inria.fr --token glrt-XXX_CHANGEME_USE_NEW_TOKEN_FOR_EACH_INSTANCE --executor docker --docker-image alpine
sed -i 's/concurrent = 1/concurrent = 15/' /etc/gitlab-runner/config.toml
/usr/local/bin/gitlab-runner run
    ",ssh-keys=andreser:ssh-ed25519\ AAAAC3NzaC1lZDI1NTE5AAAAINvz\+/Q2rsl0GwgWtrvkYNMiPq6V4yjxyLINYRnUSuqK\ andreser@work-ct \
    --no-restart-on-failure \
    --maintenance-policy=MIGRATE \
    --provisioning-model=STANDARD \
    --service-account=120707731901-compute@developer.gserviceaccount.com \
    --scopes=https://www.googleapis.com/auth/devstorage.read_only,https://www.googleapis.com/auth/logging.write,https://www.googleapis.com/auth/monitoring.write,https://www.googleapis.com/auth/servicecontrol,https://www.googleapis.com/auth/service.management.readonly,https://www.googleapis.com/auth/trace.append \
    --create-disk=auto-delete=yes,boot=yes,device-name=andreser-coq-ci-runnner-2,image=projects/debian-cloud/global/images/debian-12-bookworm-v20240910,mode=rw,size=4096,type=projects/frog-ext/zones/us-central1-a/diskTypes/pd-balanced \
    --no-shielded-secure-boot \
    --shielded-vtpm \
    --shielded-integrity-monitoring \
    --labels=goog-ec-src=vm_add-gcloud \
    --reservation-affinity=any
