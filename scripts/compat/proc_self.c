/* Optional sandbox compatibility: Lean asks for /proc/<own-pid>/exe;
 * some containers expose only /proc/self/exe. Redirect that exact query.
 * This does not change Lean's parser, elaborator, kernel, or proof objects.
 * Build: cc -shared -fPIC -o /tmp/lean-proc-self.so proc_self.c -ldl
 * Use only if needed: LD_PRELOAD=/tmp/lean-proc-self.so lake build
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    char own_exe[64];
    snprintf(own_exe, sizeof own_exe, "/proc/%ld/exe", (long)getpid());
    if (strcmp(path, own_exe) == 0) path = "/proc/self/exe";
    return original(path, buf, size);
}
