local function print(msg)
    DEFAULT_CHAT_FRAME:AddMessage(msg)
end

local _G = getfenv(0)


local libtipscan = {}
local baseName = "UIScan"
local methods = {
  "SetBagItem", "SetAction", "SetAuctionItem", "SetAuctionSellItem", "SetBuybackItem",
  "SetCraftItem", "SetCraftSpell", "SetHyperlink", "SetInboxItem", "SetInventoryItem",
  "SetLootItem", "SetLootRollItem", "SetMerchantItem", "SetPetAction", "SetPlayerBuff",
  "SetQuestItem", "SetQuestLogItem", "SetQuestRewardSpell", "SetSendMailItem", "SetShapeshift",
  "SetSpell", "SetTalent", "SetTrackingSpell", "SetTradePlayerItem", "SetTradeSkillItem", "SetTradeTargetItem",
  "SetTrainerService", "SetUnit", "SetUnitBuff", "SetUnitDebuff",
}
local extra_methods = {
  "Find", "Line", "Text", "List",
}

local getFontString = function(obj)
  local name = obj:GetName()
  local r, g, b, color, a
  local text, segment

  for i=1, obj:NumLines() do
    local left = _G[string.format("%sTextLeft%d",name,i)]
    segment = left and left:IsVisible() and left:GetText()
    segment = segment and segment ~= "" and segment or nil
    if segment then
      r, g, b, a = left:GetTextColor()
      segment = rgbhex(r,g,b) .. segment .. "|r"
      text = text and text .. "\n" .. segment or segment
    end
  end
  return text
end

local getText = function(obj)
  local name = obj:GetName()
  local text = {}
  for i=1, obj:NumLines() do
    local left, right = _G[string.format("%sTextLeft%d",name,i)], _G[string.format("%sTextRight%d",name,i)]
    left = left and left:IsVisible() and left:GetText()
    right = right and right:IsVisible() and right:GetText()
    left = left and left ~= "" and left or nil
    right = right and right ~= "" and right or nil
    if left or right then
      text[i] = {left, right}
    end
  end
  return text
end

local findText = function(obj, text, exact)
  local name = obj:GetName()
  for i=1, obj:NumLines() do
    local left, right = _G[string.format("%sTextLeft%d",name,i)], _G[string.format("%sTextRight%d",name,i)]
    left = left and left:IsVisible() and left:GetText()
    right = right and right:IsVisible() and right:GetText()
    if exact then
      if (left and left == text) or (right and right == text) then
        return i, text
      end
    else
      if left then
        local found,_,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10 = string.find(left, text)
        if found then
          return i, a1,a2,a3,a4,a5,a6,a7,a8,a9,a10
        end
      end
      if right then
        local found,_,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10 = string.find(right, text)
        if found then
          return i, a1,a2,a3,a4,a5,a6,a7,a8,a9,a10
        end
      end
    end
  end
end

local lineText = function(obj, line)
  local name = obj:GetName()
  if line <= obj:NumLines() then
    local left, right = _G[string.format("%sTextLeft%d",name,line)], _G[string.format("%sTextRight%d",name,line)]
    left = left and left:IsVisible() and left:GetText()
    right = right and right:IsVisible() and right:GetText()

    if left or right then
      return left, right
    end
  end
end

local findColor = function(obj, r,g,b)
  local name = obj:GetName()
  if type(r) == "table" then
    r,g,b = r.r or r[1], r.g or r[2], r.b or r[3]
  end
  for i=1, obj:NumLines() do
    local tr, tg, tb
    local left, right = _G[string.format("%sTextLeft%d",name,i)], _G[string.format("%sTextRight%d",name,i)]
    if left and left:IsVisible() then
      tr, tg, tb = left:GetTextColor()
      tr, tg, tb = round(tr,1), round(tg,1), round(tb,1)
    end
    if tr and (tr == r and tg == g and tb == b) then
      return i
    end
    if right and right:IsVisible() then
      tr, tg, tb = right:GetTextColor()
      tr, tg, tb = round(tr,1), round(tg,1), round(tb,1)
    end
    if tr and (tr == r and tg == g and tb == b) then
      return i
    end
  end
end

libtipscan._registry = setmetatable({},{__index = function(t,k)
  local v = CreateFrame("GameTooltip", string.format("%s%s",baseName,k), nil, "GameTooltipTemplate")
  v:SetOwner(WorldFrame,"ANCHOR_NONE")
  v:SetScript("OnHide", function ()
    this:SetOwner(WorldFrame,"ANCHOR_NONE")
  end)
  function v:Text()
    return getText(self)
  end
  function v:FontString()
    return getFontString(self)
  end
  function v:Find(text, exact)
    return findText(self, text, exact)
  end
  function v:Color(r,g,b)
    return findColor(self,r,g,b)
  end
  function v:Line(line)
    return lineText(self, line)
  end
  for _,method in ipairs(methods) do
    local method = method
    local old = v[method]
    v[method] = function(v, a1,a2,a3,a4,a5,a6,a7,a8,a9,a10)
      v:ClearLines()
      return old(v, a1,a2,a3,a4,a5,a6,a7,a8,a9,a10)
    end
  end
  function v:List()
    table.sort(methods)
    for _,method in ipairs(methods) do
      print(method)
    end
    for _,method in ipairs(extra_methods) do
      print(method)
    end
  end
  rawset(t,k,v)
  return v
end})

function libtipscan:GetScanner(type)
  local scanner = self._registry[type]
  scanner:ClearLines()
  return scanner
end

function libtipscan:List()
  for name, scanner in pairs(self._registry) do
    print(name)
  end
end





local scanner = libtipscan:GetScanner("sunderarmor")



local frame = CreateFrame("Frame")
local addon_prefix_sunder_cast = 'SACAST'

local sundercounts = {}

-- 1. Register for periodic damage events where debuff applications are logged
frame:RegisterEvent("CHAT_MSG_ADDON")
frame:RegisterEvent("CHAT_MSG_SPELL_PERIODIC_CREATURE_DAMAGE")
frame:RegisterEvent("CHAT_MSG_SPELL_PERIODIC_HOSTILEPLAYER_DAMAGE")

frame:SetScript("OnEvent", function()
    -- 1. Handle Addon Messages from OTHER warriors
    if event == 'CHAT_MSG_ADDON' and arg1 == 'SACAST' then
        local sender = arg4
        local me = UnitName("player")

        -- Only process if the message came from someone else
        if sender ~= me then
            if not sundercounts[sender] then sundercounts[sender] = 0 end
            sundercounts[sender] = sundercounts[sender] + 1
            print(string.format('%s sundered!', sender))
        end
        
    -- 2. Handle Combat Log for personal accuracy (No printing here)
    elseif event == "CHAT_MSG_SPELL_PERIODIC_CREATURE_DAMAGE" or 
           event == "CHAT_MSG_SPELL_PERIODIC_HOSTILEPLAYER_DAMAGE" then
        
        -- Use the exact 1.12.1 phrase: "is afflicted by"
        if string.find(arg1, "is afflicted by Sunder Armor") then
             local now = GetTime()
             if lastsunder and (now - lastsunder) < 0.5 then
                 -- This ensures your internal table stays accurate even if addon msgs lag
                 local me = UnitName("player")
                 if not sundercounts[me] then sundercounts[me] = 0 end
                 -- We don't increment here to avoid triple-counting with maybesunder
             end
        end
    end
end)

-- frame:SetScript("OnEvent", function()
--     -- Handle Addon Messages (Prints "Name sundered!" for you and other warriors)
--     if event == 'CHAT_MSG_ADDON' and arg1 == 'SACAST' then
--         if not sundercounts[arg4] then 
--             sundercounts[arg4] = 0 
--         end
--         sundercounts[arg4] = sundercounts[arg4] + 1
        
--         -- This line prints the name to your chat frame
--         print(string.format('%s sundered!', arg4))
        
--     -- Handle Combat Log (Keeps the internal counter accurate via timing)
--     elseif event == "CHAT_MSG_SPELL_PERIODIC_CREATURE_DAMAGE" or 
--            event == "CHAT_MSG_SPELL_PERIODIC_HOSTILEPLAYER_DAMAGE" then
        
--         if string.find(arg1, "is afflicted by Sunder Armor") then
--              local now = GetTime()
--              if lastsunder and (now - lastsunder) < 0.5 then
--                  local caster = UnitName("player")
--                  if not sundercounts[caster] then sundercounts[caster] = 0 end
--                  -- We don't print here because the Addon Message above handles it
--              end
--         end
--     end
-- end)



local spellidcache = {}

local function GetSpellCooldownByName(spellName)
    local checkFor = function(bookType)
        -- check cache first
        local spellid = spellidcache[spellName]
        if spellid then
            -- print('found in cache')
            local _, duration = GetSpellCooldown(spellid, bookType);
            return duration;
        end

        -- nothing in cache, start scanning
        local i = 1
        while true do
            local name, spellRank = GetSpellName(i, bookType);
            
            if not name then
                break;
            end
            
            if name == spellName then
                -- print(string.format('name %s rank %s', name, spellRank))
                spellidcache[name] = i
                local _, duration = GetSpellCooldown(i, bookType);
                return duration;
            end
            
            i = i + 1
        end
        return nil;
    end
    
    
    --local cd = checkFor(BOOKTYPE_PET);
    --if not cd then cd = checkFor(BOOKTYPE_SPELL); end
    local cd = checkFor(BOOKTYPE_SPELL);
    
    return cd;
end


local _ = GetSpellCooldownByName('Sunder Armor')



local hooks = {}

function hooksecurefunc(name, func, append)
  if not _G[name] then return end

  hooks[tostring(func)] = {}
  hooks[tostring(func)]["old"] = _G[name]
  hooks[tostring(func)]["new"] = func

  if append then
    hooks[tostring(func)]["function"] = function(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
      hooks[tostring(func)]["old"](a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
      hooks[tostring(func)]["new"](a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
    end
  else
    hooks[tostring(func)]["function"] = function(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
      hooks[tostring(func)]["new"](a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
      hooks[tostring(func)]["old"](a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
    end
  end

  _G[name] = hooks[tostring(func)]["function"]
end


local lastsunder = 0


local function maybesunder(spell)

    if not spell then return end
    if type(spell) ~= 'string' then return end
    -- if target == nil then return end
    --print(string.format('testing %s %s', tostring(spell), tostring(target)))
    spell = string.lower(spell)

    if not string.find(spell, 'sunder armor') then
        -- print('spell name?')
        return
    end
    -- Now we've found sunder. Check the cooldown
    local cd = GetSpellCooldownByName('Sunder Armor')
    if cd == 0 then
        -- print(string.format('cooldown? %s ', cd))
        return
    end

    -- Test for target
    if UnitCanAttack("player", "target") == nil then
        -- print('cannot attack?')
        return
    end

    local now = GetTime()
    if lastsunder + cd >= now then
        -- print('cooldown 2?')
        return
    end

    lastsunder = GetTime()

    local me = UnitName("player")
    if not sundercounts[me] then sundercounts[me] = 0 end
    sundercounts[me] = sundercounts[me] + 1

    -- This sends the hidden message so other warriors' addons see it
    SendAddonMessage(addon_prefix_sunder_cast, 'whatever', "RAID")
    
    -- Use UnitName("player") to correctly print your own name
    print(string.format('%s sundered!', UnitName("player")))
end


hooksecurefunc("UseAction", function(slot, target, button)
    --print(string.format("%s %s %s", tostring(slot), tostring(target), tostring(button)))

    scanner:SetAction(slot)
    local spell, rank = scanner:Line(1)

    local text = GetActionText(slot)
    -- print(string.format("action text %s", tostring(text)))
    if text or not IsCurrentAction(slot) then return end

    maybesunder(spell)
end, true)


hooksecurefunc("CastSpell", function(spellid, bookType)
    local spell = 'Sunder Armor'
    if spellidcache[spell] ~= spellid then return end
    maybesunder(spell)
end, true)


hooksecurefunc("CastSpellByName", function(spell, target)
    maybesunder(spell)
end, true)


local function resetcounts()
    sundercounts = {}
    print('sunder counts reset')
end



local function dumpcounts()
    print('sunder counts:')
    local len = 0
    for k, v in pairs(sundercounts) do
        print(string.format('%s %s', k, v))
        len = len + 1
    end
    if len == 0 then
        print('no data')
    end
    print('sunder counts end')
end

-- 2. Register the slash command (use uppercase for the ID)
SLASH_SUNDERCOUNT1 = "/sundercount";
SLASH_SUNDERCOUNT2 = "/sundercounts";
SlashCmdList["SUNDERCOUNT"] = dumpcounts


SLASH_SUNDERRESET1 = "/sunderreset";
SlashCmdList["SUNDERRESET"] = resetcounts
