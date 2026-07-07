/* Minimal eBPF loader for differential testing of the M1 arithmetic
 * checker against the kernel verifier.
 *
 * usage: loader <hex-bytecode> [-v]
 *   <hex-bytecode>: whole program as hex (16 hex chars per instruction)
 *   -v: dump the verifier log to stderr
 *
 * prints ACCEPT or "REJECT errno=.." on stdout; exit code 0/1/2.
 * Loads as BPF_PROG_TYPE_SOCKET_FILTER (simplest context; arithmetic-only
 * programs never touch ctx). Run as root.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <linux/bpf.h>
#include <sys/syscall.h>

static int sys_bpf(int cmd, union bpf_attr *attr, unsigned int size)
{
	return syscall(__NR_bpf, cmd, attr, size);
}

static char vlog[1 << 20];

int main(int argc, char **argv)
{
	if (argc < 2) {
		fprintf(stderr, "usage: %s <hex> [-v]\n", argv[0]);
		return 2;
	}
	const char *hex = argv[1];
	size_t hl = strlen(hex);
	if (hl == 0 || hl % 16 != 0) {
		fprintf(stderr, "hex length must be a positive multiple of 16\n");
		return 2;
	}
	size_t nbytes = hl / 2;
	unsigned char *buf = malloc(nbytes);
	if (!buf)
		return 2;
	for (size_t i = 0; i < nbytes; i++) {
		if (sscanf(hex + 2 * i, "%2hhx", &buf[i]) != 1) {
			fprintf(stderr, "bad hex at offset %zu\n", 2 * i);
			return 2;
		}
	}

	union bpf_attr attr;
	memset(&attr, 0, sizeof(attr));
	attr.prog_type = BPF_PROG_TYPE_SOCKET_FILTER;
	attr.insn_cnt = nbytes / 8;
	attr.insns = (unsigned long)buf;
	attr.license = (unsigned long)"GPL";
	attr.log_buf = (unsigned long)vlog;
	attr.log_size = sizeof(vlog);
	attr.log_level = 2;
	strncpy(attr.prog_name, "m1diff", sizeof(attr.prog_name) - 1);

	int fd = sys_bpf(BPF_PROG_LOAD, &attr, sizeof(attr));
	if (fd >= 0) {
		printf("ACCEPT\n");
		close(fd);
	} else {
		printf("REJECT errno=%d (%s)\n", errno, strerror(errno));
	}
	if (argc > 2 && !strcmp(argv[2], "-v"))
		fputs(vlog, stderr);
	return fd >= 0 ? 0 : 1;
}
