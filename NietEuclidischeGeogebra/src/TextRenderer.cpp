#include "TextRenderer.h"
#include "stb/stb_image.h"

#include "Constants.h"
#include "Util.h"
#include "Application.h"

TextRenderer::TextRenderer(const std::string& fontName)
	: m_TextShader("textShader"), m_Font(std::make_shared<Font>(fontName))
{
	m_TextShader.SetUniform("u_TextImage", 0);

	unsigned int indices[6]{ 0,1,2,2,3,0 };

	glGenVertexArrays(1, &m_Vao);
	glBindVertexArray(m_Vao);

	glGenBuffers(1, &m_Vb);
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferData(GL_ARRAY_BUFFER, 16 * sizeof(float), NULL, GL_DYNAMIC_DRAW);

	glEnableVertexAttribArray(0);
	glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, 4 * sizeof(float), 0);
	glEnableVertexAttribArray(1);
	glVertexAttribPointer(1, 2, GL_FLOAT, GL_FALSE, 4 * sizeof(float), (void*)(2 * sizeof(float)));

	glGenBuffers(1, &m_Ib);
	glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, m_Ib);
	glBufferData(GL_ELEMENT_ARRAY_BUFFER, 6 * sizeof(unsigned int), indices, GL_STATIC_DRAW);
}

TextRenderer::~TextRenderer()
{
	glDeleteBuffers(1, &m_Vb);
	glDeleteBuffers(1, &m_Ib);
	glDeleteVertexArrays(1, &m_Vao);
}

void TextRenderer::AddToRenderQueue(const std::shared_ptr<Text>& m_Text)
{
	m_RenderQueue.push(m_Text);
}

void TextRenderer::RenderQueue()
{
	m_TextShader.Bind();
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, m_Font->GetBitmap());
	glBindVertexArray(m_Vao);
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb); // Vertex buffers are not kept in the vertex array object and are not required for rendering. We do need it here so we need to explicitly bind it
	std::shared_ptr<Font> font = Application::Get()->GetRenderer()->GetFont();
	auto [width, height] = Application::Get()->GetWindow()->GetSize();
	while (m_RenderQueue.size() != 0)
	{
		std::shared_ptr<Text> t = m_RenderQueue.front();
		m_RenderQueue.pop();

		float scale = (float)t->m_Size / font->GetSize();
		float currentX = t->m_LeftX;
		float currentY = t->m_Baseline;
		for (int i{ t->m_RenderBegin }; i < t->m_RenderEnd; ++i)
		{
			int c = t->m_Text[i];
			const CharacterInfo& info{ font->GetCharacterInfo(c) };

			float charLeftX = currentX + (float)info.xOffset / width * scale;
			float charRightX = charLeftX + (float)info.width / width * scale;
			if (charRightX > t->m_RightX)
			{
				currentX = t->m_LeftX;
				currentY -= (float)font->GetLineHeight() / height * scale;
				charLeftX = currentX + (float)info.xOffset / width * scale;
				charRightX = charLeftX + (float)info.width / width * scale;
			}
			float charTopY = currentY + (float)font->GetBase() / height * scale - (float)info.yOffset / height * scale;
			float charBottomY = charTopY - (float)info.height / height * scale;

			float texLeftX = (float)info.x / font->GetWidth();
			float texRightX = texLeftX + (float)info.width / font->GetWidth();
			float texTopY = 1 - ((float)info.y / font->GetHeight());
			float texBottomY = texTopY - (float)info.height / font->GetHeight();

			float data[16] = {
				charLeftX,  charBottomY,	texLeftX,  texBottomY,
				charRightX, charBottomY,	texRightX, texBottomY,
				charRightX, charTopY,		texRightX, texTopY,
				charLeftX,  charTopY,		texLeftX,  texTopY
			};
			currentX += (((float)info.xAdvance) / width) * scale;

			glBufferSubData(GL_ARRAY_BUFFER, 0, 16 * sizeof(float), data);
			glDrawElements(GL_TRIANGLES, 6, GL_UNSIGNED_INT, nullptr);
		}
	}
}

Font::Font(const std::string& fontName)
	: m_LineHeight{ -1 }, m_Size{ -1 }, m_Base{ -1 }
{
	std::ifstream file(AssetsFolder + "/fonts/" + fontName + "/info.txt");
	if (!file)
		throw std::runtime_error("Failed to load info for font" + fontName);

	std::string word;
	while (file >> word)
	{
		if (word.compare(0, 5, "face=") == 0)
		{
			m_BaseFont = word.substr(5);
		}
		else if (word.compare(0, 11, "lineHeight=") == 0)
		{
			m_LineHeight = std::atoi(&word[11]);
		}
		else if (word.compare(0, 5, "size=") == 0)
		{
			m_Size = std::atoi(&word[5]);
		}
		else if (word.compare(0, 5, "base=") == 0)
		{
			m_Base = std::atoi(&word[5]);
		}
		else if (word.compare(0, 4, "char") == 0)
		{
			std::string line;
			std::getline(file, line);
			CharacterInfo info;
			int character;
			std::string word;
			std::stringstream lineS;
			lineS << line;
			while (lineS >> word)
			{
				if (word.compare(0, 3, "id=") == 0)
					character = std::atoi(&word[3]);
				else if (word.compare(0, 2, "x=") == 0)
					info.x = std::atoi(&word[2]);
				else if (word.compare(0, 2, "y=") == 0)
					info.y = std::atoi(&word[2]);
				else if (word.compare(0, 6, "width=") == 0)
					info.width = std::atoi(&word[6]);
				else if (word.compare(0, 7, "height=") == 0)
					info.height = std::atoi(&word[7]);
				else if (word.compare(0, 8, "xoffset=") == 0)
					info.xOffset = std::atoi(&word[8]);
				else if (word.compare(0, 8, "yoffset=") == 0)
					info.yOffset = std::atoi(&word[8]);
				else if (word.compare(0, 9, "xadvance=") == 0)
					info.xAdvance = std::atoi(&word[9]);
				else if (word.compare(0, 5, "page=") == 0)
					info.page = std::atoi(&word[5]);
				else if (word.compare(0, 5, "chnl=") == 0)
					info.channel = std::atoi(&word[5]);
			}
			m_CharacterInformation.insert({ character, info });
		}
	}

	int width, height, numChannels;
	stbi_set_flip_vertically_on_load(true);
	unsigned char* data{ stbi_load((AssetsFolder + "/fonts/" + fontName + "/bitmap.png").c_str(), &width, &height, &numChannels, 0) };
	if (!data)
		throw std::runtime_error("Failed to load bitmap for font: " + fontName);
	m_TotalHeight = height;
	m_TotalWidth = width;

	GLint imageType;
	switch (numChannels)
	{
	case 1:
		imageType = GL_R;
		break;
	case 2:
		imageType = GL_RG;
		break;
	case 3:
		imageType = GL_RGB;
		break;
	case 4:
		imageType = GL_RGBA;
		break;
	default:
		throw std::runtime_error("Weird number of channels " + std::to_string(numChannels) + " from font " + fontName);
	}
	glGenTextures(1, &m_Bitmap);
	glBindTexture(GL_TEXTURE_2D, m_Bitmap);

	// These first two should really not matter
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_REPEAT);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_REPEAT);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexImage2D(GL_TEXTURE_2D, 0, imageType, width, height, 0, imageType, GL_UNSIGNED_BYTE, data);
	//glGenerateMipmap(GL_TEXTURE_2D);

	stbi_image_free(data);
}

Font::~Font()
{
	glDeleteTextures(1, &m_Bitmap);
}

CharacterInfo Font::GetCharacterInfo(int character)
{
	auto it = m_CharacterInformation.find(character);
	if (it == m_CharacterInformation.end())
	{
		throw std::runtime_error(std::string("Unkown character ") + (char)character + " with code " + std::to_string(character));
	}
	return it->second;
}

Text::Text(const std::string& text, float leftX, float rightX, float baseLine, float size)
	: Text(AdvancedString(text), leftX, rightX, baseLine, size)
{
}

Text::Text(const AdvancedString& letters, float leftX, float rightX, float baseLine, float size)
	: m_Text{ letters }, m_LeftX{ leftX }, m_RightX{ rightX }, m_Baseline{ baseLine }, m_Size{ size }, m_RenderBegin{ 0 }, m_RenderEnd{ (int)letters.size() }
{
	std::shared_ptr<Font> font = Application::Get()->GetRenderer()->GetFont();
	auto [width, height] = Application::Get()->GetWindow()->GetSize();

	float scale = (float)m_Size / font->GetSize();
	m_Scale = scale;
}

Text::~Text()
{
}

void Text::AddText(const AdvancedString& letters, int position)
{
	m_Text.insert(m_Text.begin()+position, letters.begin(), letters.end());
	/*
	std::vector<int> text;
	text.resize(letters.size());
	for (int i{ 0 }; i < letters.size(); ++i)
	{
		text[i] = letters[i];
	}

	std::shared_ptr<Font> font = Application::Get()->GetRenderer()->GetFont();
	auto [width, height] = Application::Get()->GetWindow()->GetSize();
	for (int i{ 0 }; i < letters.size(); ++i)
	{
		int c = letters[i];
		const CharacterInfo& info{ font->GetCharacterInfo(c) };
		text[i].second = (float)info.xAdvance * m_Scale;
	}
	m_Text.insert(m_Text.begin() + position, text.begin(), text.end());*/
}

void Text::AddText(const std::string& letters, int position)
{
	AddText(AdvancedString{letters}, position);
}

void Text::RemoveText(int begin, int num)
{
	m_Text.erase(m_Text.begin() + begin, m_Text.begin() + begin + num);
}
