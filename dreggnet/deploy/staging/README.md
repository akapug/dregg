# DreggNet — STAGING deploy

A not-yet-continuous staging environment on one cheap AWS box: the DreggNet
serving stack (gateway + operator CLI + Postgres) **plus** a dregg node (the
substrate the bridge/leases talk to), wired together for end-to-end iteration.

The design principle: **the box just RUNS.** Heavy compilation happens on your
Mac (cross-build) or a Lean-capable builder (the node image); the box only pulls
images and runs `docker compose up`. A 2 GB box OOMs building the DreggNet/net
Rust closure, so we never build Rust there.

## The two halves (and why they ship differently)

| Piece | How it gets to the box | Why |
|---|---|---|
| `dreggnet-gateway`, `dreggnet` (cli) | **cross-build locally** with `cargo zigbuild --target x86_64-unknown-linux-gnu`, rsync the binaries, wrap in `debian-slim` via `Dockerfile.runtime` | pure cross-compilable Rust; small, fast |
| Postgres | `postgres:16-bookworm` image (pulled) | stock |
| `dregg-node` | **pre-built linux/amd64 image** (registry pull or `docker save`/`load`) | links a **host-native Lean archive** — see below |

### The dregg node — not cross-compilable

`dregg-node` links `libdregg_lean.a` (the native objects the Lean compiler emits
for the verified kernel + its mathlib closure) **unconditionally** on native.
That archive is host-architecture objects and **cannot be cross-compiled**
(breadstuffs `node/Cargo.toml` says so explicitly: aarch64 and cross targets are
blocked). `cargo zigbuild` of `dregg-node` from an arm64 Mac would try to link
arm64 objects into an x86_64 ELF and fail.

So the node ships as a **pre-built linux/amd64 image**, built where a Lean
toolchain lives (elan/lake + warm mathlib). From the breadstuffs repo:

```sh
cd ~/dev/breadstuffs
# On a Lean-capable linux/amd64 builder (CI runner or an x86_64 EC2 build box).
# NOTE: breadstuffs docker/Dockerfile installs rust+nightly but NOT elan/lake;
# add the Lean toolchain to the builder (or extend that Dockerfile) so build.rs
# can splice the x86_64 Lean archive.
docker buildx build --platform linux/amd64 --target node \
  -f docker/Dockerfile -t <registry>/dregg-node:staging --push .
```

Then either push to GHCR/ECR, or ship the image directly:

```sh
docker save <registry>/dregg-node:staging | \
  ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<box> docker load
```

and set `DREGG_NODE_IMAGE` in `.env`. Until that image exists the gateway + cli +
Postgres half runs fine on its own; the `dregg-node` service is the only piece
that needs it.

## Deploy (from your Mac)

```sh
cp deploy/staging/.env.example deploy/staging/.env   # fill DREGG_NODE_IMAGE
BOX_HOST=<BUILDER_HOST> \
SSH_KEY=~/.ssh/dreggnet-staging.pem \
  deploy/staging/deploy.sh            # build (zigbuild) + ship (rsync) + up
```

Sub-commands: `deploy.sh {build|ship|up|down|logs|build-node}`.

Once up:

```sh
curl -s http://<box>:8080/v1/apps/demo/machines        # the machines API
ssh ... 'cd /opt/dreggnet && docker compose exec dreggnet dreggnet-demo'  # e2e demo
curl -s http://<box>:8420/health                       # the dregg node
```

## ⚠ Dependency: exec-green

The gateway + cli cross-build pulls the `exec/` → polyana closure. The
polyana-improvement lane is mid-flight on `exec/`, so a **cold cross-build may
transiently fail** until that lane is green. The deploy script fails loudly
(no stale-artifact fallback) rather than ship a half-built binary. The node,
gateway, and cli are the stable surfaces; the *full* end-to-end deploy waits on
`exec/` being green. (The Postgres + node-image half does not depend on it.)

## Cost analysis

us-east-1 on-demand, Linux, as of 2026-06. "Stopped" = you pay only for the
EBS root volume (~$0.08/GB-month × 20 GB ≈ **$1.60/mo**), not the instance.

| Instance | vCPU / RAM | On-demand $/hr | 24×7 $/mo | Stopped-when-idle* | Spot ~⅓ |
|---|---|---|---|---|---|
| t3.small | 2 / 2 GB | $0.0208 | ~$15 | ~$5 + $1.60 EBS | ~$5/mo |
| **t3.medium** (provisioned) | 2 / 4 GB | $0.0416 | ~$30 | ~$8 + $1.60 EBS | ~$10/mo |

\* "stopped-when-idle" assumes ~8 h/day of running. Stop the box when you're not
iterating; binaries + volumes persist.

**Sizing:** a *run-only* box that ships binaries can be **t3.small** (2 GB) if
you run only gateway + cli + Postgres. We provisioned **t3.medium** (4 GB)
because the **dregg-node links the Lean runtime and can STARK-prove turns**
(`DREGG_PROVE_TURNS=1`), which is memory-hungry — 2 GB would thrash. For a
gateway-only staging box, downgrade to t3.small to halve the bill. To resize:
stop the instance, `aws ec2 modify-instance-attribute --instance-id <id>
--instance-type '{"Value":"t3.small"}'`, start it.

## What was provisioned

A live t3.medium staging box (us-east-1):

- **Instance:** `<INSTANCE_ID>` (t3.medium, us-east-1c)
- **Public IP / DNS:** `<BUILDER_HOST>` / `<BUILDER_HOST>`
- **AMI:** `ami-0a02a779008fa3b99` (Ubuntu 24.04 LTS amd64)
- **Key pair:** `dreggnet-staging` → `~/.ssh/dreggnet-staging.pem`
- **Security group:** `sg-0d76f69da366c1e91` — ingress 22 (ssh), 8080 (gateway),
  8420 (node API), 9420 (node gossip), all from `0.0.0.0/0`
- **Root volume:** 20 GB gp3
- **User-data:** installs Docker CE + compose plugin + rsync; creates `/opt/dreggnet`
- **Running cost:** ~$0.0416/hr ≈ **$30/mo** if left on; ~$1.60/mo if stopped.

> ⚠ Security: SSH (22) is open to `0.0.0.0/0` for deploy convenience. Tighten to
> your IP for anything that lives:
> `aws ec2 authorize-security-group-ingress --group-id sg-0d76f69da366c1e91 --protocol tcp --port 22 --cidr <your-ip>/32`
> (and revoke the `0.0.0.0/0` rule).

### Manage the box

```sh
REGION=us-east-1; IID=<INSTANCE_ID>
aws ec2 stop-instances      --region $REGION --instance-ids $IID   # stop billing (keep disk)
aws ec2 start-instances     --region $REGION --instance-ids $IID   # resume
aws ec2 describe-instances  --region $REGION --instance-ids $IID \
  --query 'Reservations[0].Instances[0].{state:State.Name,ip:PublicIpAddress}' --output table
aws ec2 terminate-instances --region $REGION --instance-ids $IID   # destroy (irreversible)
```

> A stopped instance gets a **new public IP** on next start. Re-read the IP after
> `start-instances`, or attach an Elastic IP if you want it stable.

## Provision from scratch (the exact commands)

Already run for the box above; here for reproducibility / a second box.

```sh
REGION=us-east-1
VPC=$(aws ec2 describe-vpcs --region $REGION --filters Name=isDefault,Values=true --query 'Vpcs[0].VpcId' --output text)
AMI=$(aws ssm get-parameter --region $REGION \
  --name /aws/service/canonical/ubuntu/server/24.04/stable/current/amd64/hvm/ebs-gp3/ami-id \
  --query 'Parameter.Value' --output text)

# key pair (private key saved locally, chmod 600)
aws ec2 create-key-pair --region $REGION --key-name dreggnet-staging \
  --query KeyMaterial --output text > ~/.ssh/dreggnet-staging.pem && chmod 600 ~/.ssh/dreggnet-staging.pem

# security group
SG=$(aws ec2 create-security-group --region $REGION --group-name dreggnet-staging-sg \
  --description "DreggNet staging" --vpc-id $VPC --query GroupId --output text)
for p in 22 8080 8420 9420; do
  aws ec2 authorize-security-group-ingress --region $REGION --group-id $SG --protocol tcp --port $p --cidr 0.0.0.0/0
done

# launch (user-data installs docker; see deploy.sh comments)
aws ec2 run-instances --region $REGION \
  --image-id $AMI --instance-type t3.medium --count 1 \
  --key-name dreggnet-staging --security-group-ids $SG \
  --block-device-mappings '[{"DeviceName":"/dev/sda1","Ebs":{"VolumeSize":20,"VolumeType":"gp3","DeleteOnTermination":true}}]' \
  --tag-specifications 'ResourceType=instance,Tags=[{Key=dreggnet,Value=staging},{Key=Name,Value=dreggnet-staging}]' \
  --user-data file://<(printf '#!/bin/bash\napt-get update && apt-get install -y docker.io docker-compose-v2 rsync && usermod -aG docker ubuntu && systemctl enable --now docker && mkdir -p /opt/dreggnet && chown ubuntu /opt/dreggnet\n') \
  --query 'Instances[0].InstanceId' --output text
```
