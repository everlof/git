#ifndef UPLOAD_PACK_H
#define UPLOAD_PACK_H

struct repository;
struct argv_array;
extern int upload_pack_v2(struct repository *r, struct argv_array *keys,
			  struct argv_array *args);

#endif /* UPLOAD_PACK_H */
