import uuid
import zeroconf
import traceback


CL_PORT = 12345
HEARTBEAT_TTL = 10


class MutexInfo(object):
    def __init__(self, uuid):
        self.uuid = uuid
        self.service = None
        self.queue = []
        self.counter = 0
        self.queues = {}
        self.watchdog = None


class LockDirectory(dict):
    def __getitem__(self, key):
        if key not in self:
            self[key] = LockDaemon(key)
        return dict.__getitem__(self, key)


class LockDaemon(object):
    def __init__(self, mdns=None):
        self.mdns = mdns or zeroconf.Zeroconf(heartbeat=True)

    def get_ring(self, domain):
        ring = sorted(self.mdns.lookupPTR(domain))
        return [x[0] for x in ring]

    def get_leader(self):
        pass

    def start_election(self):
        pass

    def register(self, mutex):
        if mutex.domain not in self.ds:
            info = self.ds[mutex.domain] = MutexInfo(mutex.uuid)

            try:
                info.service = zeroconf.ServiceInfo(
                        type="%s" % (mutex.domain),
                        name="%s.%s" % (mutex.uuid, mutex.domain),
                        address=[],
                        port=CL_PORT,
                        weight=0,
                        priority=0,
                        properties={
                            "role": "candidate",
                            "alias": self.alias},
                        records=[zeroconf._TYPE_TXT],
                        ttl=HEARTBEAT_TTL,
                        signer=self.alias)
                self.mdns.registerService(info.service)
            except Exception as e:
                del self.ds[mutex.domain]
                traceback.print_exc()
                raise e

    def acquire(self, mutex):
        pass

    def release(self, mutex):
        pass


class Lock(object):

    def __init__(self, daemon=None):
        self.daemon = daemon or _lock_daemons["default"]
        self.uuid = uuid.uuid4()
        self.domain = "_cx._udp.local"
        self.daemon.register(self)

    def acquire(self):
        self.daemon.acquire(self)

    def release(self):
        self.daemon.release(self)


class Event(object):
    pass


_lock_daemons = LockDirectory()
