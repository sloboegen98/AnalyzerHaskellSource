import asyncio

async def periodic():
    while True:
        print('periodic')
        await asyncio.sleep(1)

def stop():
    task.cancel()

loop = asyncio.get_event_loop()
task = loop.create_task(periodic())
loop.call_later(5, task.cancel)

try:
    loop.run_until_complete(task)
except asyncio.CancelledError:
    pass