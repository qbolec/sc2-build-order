struct FreeSlot{
  FreeSlot * next;
  FreeSlot ** pointer_to_pointer_to_me;
};
template<uint32 total_size>
struct Slab{
  union{
    Slab * next_free;
    uint32 usage;
  };
  uint32 element_size;
  char data[total_size];
public:
  Slab():next_free(NULL),element_size(0){
  }
  void on_alloc(){
    ++usage;
  }
  void on_free(){
    --usage;
    
  }
  void clear(){
    assert(0==usage);
    const uint32 elements_count=total_size/element_size;
    for(uint32 i=0;i<elements_count;++i){
      FreeSlot * slot = (FreeSlot *)&data[i*element_size];
      assert(NULL!=slot);
      assert(NULL!=slot->pointer_to_pointer_to_me);
      *(slot->pointer_to_pointer_to_me)=slot->next;
      if(slot->next){
        slot->next->pointer_to_pointer_to_me=slot->pointer_to_pointer_to_me;
      }
    }
    element_size=0;
  }
  void format(uint32 element_size,FreeSlot ** pointer_to_pointer_to_free){
    const uint32 elements_count=total_size/element_size;
    assert(NULL!=this);
    this->usage = 0;
    this->element_size = element_size;
    assert(NULL!=pointer_to_pointer_to_free);
    FreeSlot * next_free = *pointer_to_pointer_to_free;
    for(uint32 i=0;i<elements_count;++i){
      FreeSlot * slot = (FreeSlot *)&data[i*element_size];
      assert(NULL!=slot);
      slot->next = next_free;
      if(NULL!=next_free){
        next_free->pointer_to_pointer_to_me = &slot->next;
      }
      next_free = slot;
    }
    assert(NULL!=pointer_to_pointer_to_free);
    *pointer_to_pointer_to_free = next_free;
    assert(NULL!=next_free);
    next_free->pointer_to_pointer_to_me=pointer_to_pointer_to_free;
  }
};

struct HeadOfSize{
  uint32 element_size;
  FreeSlot * head;
};

template<uint32 slabs_count,uint32 slab_size>
struct Slabocator{
  typedef Slab<slab_size> SlabType;
  SlabType slabs[slabs_count];
  static const uint32 MAX_HEADS=1024;
  HeadOfSize heads[MAX_HEADS];
  uint32 heads_count;
  SlabType * free_slab;
  uint32 slabs_used;
  uint32 max_slabs_used;
  HeadOfSize * find_head_of_size(uint32 element_size){
    for(uint32 i=0;i<MAX_HEADS;++i){
      if(heads[i].element_size == element_size){
        return &heads[i];
      }
    }
    return NULL;
  }
public:
  Slabocator(){
    heads_count=0;
    slabs_used=0;
    max_slabs_used=0;
    memset(heads,0,sizeof(heads));
    memset(slabs,0,sizeof(slabs));
    free_slab = NULL;
    for(uint32 i=0;i<slabs_count;++i){
      slabs[i].next_free = free_slab;
      free_slab=&slabs[i];
    }
    
  }
  void * allocate(uint32 size){
    ctrace.enter();
    //ctrace << "allocating " << size << endl;
    const uint32 element_size = (size+7)/8*8;
    HeadOfSize * head = find_head_of_size(element_size);
    if(NULL==head){
      //ctrace << "creating head entry for " << element_size << endl;
      assert(heads_count<MAX_HEADS);
      heads[heads_count].element_size = element_size;
      heads[heads_count].head = NULL;
      head = &heads[heads_count];
      ++heads_count;
    }
    assert(NULL!=head);
    if(NULL==head->head){
      //ctrace << "allocating slab for " << element_size << endl;
      assert(NULL!=free_slab);
      SlabType * slab = free_slab;
      free_slab = free_slab->next_free;
      slab->format(element_size,&(head->head));
      ++slabs_used;
      max_slabs_used=max(max_slabs_used,slabs_used);
    }
    assert(NULL!=head->head);
    void * allocated = head->head;
    head->head = head->head->next;
    if(NULL!=head->head){
      head->head->pointer_to_pointer_to_me = &(head->head);
    }
    const uint32 slab_index=get_slab_index(allocated);
    slabs[slab_index].on_alloc();
    ctrace.leave();
    return allocated;
  }
  uint32 get_slab_index(void *p){
    return ((char*)p-((char*)(&slabs[0])))/sizeof(SlabType);
  }
  void free(void * p){
    ctrace.enter();
    //ctrace << "free" << endl;
    assert(contains(p));
    const uint32 slab_index=get_slab_index(p);
    const uint32 element_size=slabs[slab_index].element_size;
    HeadOfSize * head = find_head_of_size(element_size);
    assert(NULL!=head);
    FreeSlot * slot = (FreeSlot *)p;
    assert(NULL!=slot);
    slot->next = head->head;
    if(NULL!=slot->next){
      slot->next->pointer_to_pointer_to_me = &(slot->next);
    }
    head->head = slot;
    slot->pointer_to_pointer_to_me = &(head->head);
    slabs[slab_index].on_free();
    if(0==slabs[slab_index].usage){
      //ctrace << "deallocating slab for " << element_size << endl;
      slabs[slab_index].clear();
      slabs[slab_index].next_free = free_slab;
      free_slab = &slabs[slab_index];
      --slabs_used;
      
    }
    ctrace.leave();
  }
  bool contains(void *p){
    return (void*)&slabs[0]<=p && p<(void*)&slabs[slabs_count];
  }
  void show_stats(ostream & sout){
    sout << "using " << slabs_used << " to " << max_slabs_used << " of " << slabs_count << " slabs and " << heads_count << " of " << MAX_HEADS << " heads" << endl;
  }
};
